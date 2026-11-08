;;; ajnc.el --- A Janet (Spork) Netrepl Client -*- lexical-binding: t; -*-

;; Author: nik gaffney <nik@fo.am>
;; Maintainer: nik gaffney <nik@fo.am>
;; Keywords: tools, programming, janet, repl, netrepl
;; Homepage: https://codeberg.org/zzkt/ajnc
;; Version: 20260907
;; Package-Requires: ((emacs "28.1"))

;;; Commentary:

;; A Janet (Spork) Netrepl Client.
;;
;; To start a janet repl, `M-x run-janet', to open a connection to a running
;; netrepl server, `M-x ajnc' or `M-x ajnc-connect' in a source buffer.
;;
;; See the README for full usage and protocol notes.

;;; License:
;;
;; This file is NOT part of GNU Emacs.
;; SPDX-License-Identifier: EUPL-1.2

;;; Code:

(require 'thingatpt)
(require 'comint)
(require 'subr-x)
(require 'term)


;;; Customization

(defgroup ajnc nil
  "A Janet (Spork) Netrepl Client."
  :prefix "ajnc-"
  :group 'applications)

;; endpoint and server

(defcustom ajnc-default-endpoint "localhost:9365"
  "Default host and port for the netrepl server (e.g. localhost:9365)."
  :type 'string
  :group 'ajnc)

(defcustom ajnc-netrepl-server-command "janet-netrepl -H %h -P %p"
  "Command used to start a netrepl server (use %h for host and %p for port)."
  :type 'string
  :group 'ajnc)

(defcustom ajnc-netrepl-server-buffer-name "*ajnc-server*"
  "Name of the buffer where a netrepl server process runs."
  :type 'string
  :group 'ajnc)

(defcustom ajnc-start-timeout 10
  "Time in seconds to wait for the netrepl server to start."
  :type 'integer
  :group 'ajnc)

(defcustom ajnc-client-name "janet"
  "Client name reported to the netrepl server on connection."
  :type 'string
  :group 'ajnc)


;; streamed output

(defcustom ajnc-split-stream-output nil
  "When non-nil, route streamed output to a separate buffer.
With this option enabled stream messages are appended to a separate buffer,
while prompts, echoed input, and immediate-eval results stay in the REPL."
  :type 'boolean
  :group 'ajnc)

(defcustom ajnc-colorize-output t
  "When non-nil, keep and colorize ANSI escapes in streamed output.
Enables coloured output in the REPL, the SGR codes are mapped to themeable faces
using `term-color-*'. When nil, all escapes are stripped."
  :type 'boolean
  :group 'ajnc)

(defcustom ajnc-stream-output-buffer-name "*ajnc-stream*"
  "Name of the buffer for stream output (see `ajnc-split-stream-output')."
  :type 'string
  :group 'ajnc)

;; faces

(defface ajnc-repl-result-face
  '((((class color) (min-colors 88)) :inherit font-lock-constant-face :weight bold)
    (t :inherit font-lock-constant-face))
  "Face used for immediate-eval results in the REPL."
  :group 'ajnc)

(defface ajnc-stream-face
  '((t :inherit shadow))
  "Face used for streamed output in `ajnc-stream-output-buffer-name'."
  :group 'ajnc)


;;; Buffer-local REPL state

(defvar ajnc-repl-process-name "ajnc-repl-process"
  "Name of repl process.")

(defvar ajnc-repl-buffer-name "*janet-repl*"
  "Name of repl buffer.")

(defvar-local ajnc-repl-buffer nil
  "Use multiple REPL buffers bound locally to source buffers.
When non-nil the sending and switching commands in a specific buffer
will target a named REPL. When nil, the default names are used, as
set in  `ajnc-repl-buffer-name'.")

(defvar-local ajnc-repl-port nil
  "Netrepl server port used by the REPL bound to buffer.
Set by `ajnc--connect'; nil in buffers without a REPL.")

(defun ajnc--repl-buffer-name-for (buffer)
  "Return the name of the REPL buffer bound to BUFFER.
Use buffer-local `ajnc-repl-buffer' in BUFFER, else `ajnc-repl-buffer-name'."
  (let ((bound (buffer-local-value 'ajnc-repl-buffer buffer)))
    (cond ((buffer-live-p bound) (buffer-name bound))
          ((stringp bound) bound)
          (t ajnc-repl-buffer-name))))

(defun ajnc--repl-buffer ()
  "Return the REPL buffer bound to the current buffer, or nil."
  (get-buffer (ajnc--repl-buffer-name-for (current-buffer))))

(defvar ajnc-netrepl-server-process-name "janet-netrepl-server"
  "Name of the netrepl server process.")

(defvar ajnc--debug nil
  "If non-nil, output debug info to *Messages* buffer.")


;;; Wire protocol

(defun ajnc--header (len)
  "Return the 4-byte little-endian length header for a message of LEN bytes."
  (unibyte-string (logand len #xff)
                  (logand (ash len -8) #xff)
                  (logand (ash len -16) #xff)
                  (logand (ash len -24) #xff)))

(defun ajnc--frame (payload)
  "Prepend a 4-byte little-endian length header to PAYLOAD."
  (concat (ajnc--header (string-bytes payload)) payload))

(defun ajnc--decode-header (header)
  "Decode the 4-byte little-endian message length in HEADER."
  (when ajnc--debug
    (message "header: %s" (ajnc--hexstring header)))
  (+ (aref header 0)
     (ash (aref header 1) 8)
     (ash (aref header 2) 16)
     (ash (aref header 3) 24)))


;; protocol debugging

(defun ajnc--hexstring (string)
  "Convert a STRING to sequence of hex values."
  (mapconcat (lambda (x) (format "%02X " x)) (string-to-list string)))

;; Message reassembly across chunk boundaries.

;; Message reassembly state for `ajnc--parse'.
;; Network reads arrive in arbitrarily sized chunks, so the parser
;; keeps any trailing partial message across calls.

(defvar ajnc--recv-header "")
(defvar ajnc--recv-body "")
(defvar ajnc--recv-held nil)

(defun ajnc--recv-reset ()
  "Reset message receiving state."
  (setq ajnc--recv-header "")
  (setq ajnc--recv-body "")
  (setq ajnc--recv-held nil))

(defun ajnc--parse (in-bytes)
  "Parse IN-BYTES into complete netrepl message payloads.
Holds partial headers and bodies for the next call, returned
payloads keep their leading type byte (0xFF or 0xFE) intact."
  (when ajnc--debug
    (message "Ajnc: length in-bytes: %d" (string-bytes in-bytes)))
  (let* ((s in-bytes)
         (s-len (string-bytes s))
         (pos 0)
         (remaining s-len)
         (hdr-bytes (string-bytes ajnc--recv-header))
         ;; messages completed in this call, in reverse order,
         ;; prepended with any previous partial messages.
         (completed (nreverse ajnc--recv-held))
         ;; set to t when bytes stop exactly on a message boundary.
         (boundary-stop nil))
    (setq ajnc--recv-held nil)
    (catch 'done
      (while t
        (if (< hdr-bytes 4)
            ;; header: length bytes
            (let* ((missing (- 4 hdr-bytes))
                   (take (min missing remaining)))
              (setq pos (+ pos take))
              (setq remaining (- remaining take))
              (setq hdr-bytes (+ hdr-bytes take))
              (setq ajnc--recv-header
                    (concat ajnc--recv-header
                            (substring s (- pos take) pos)))
              (when (< hdr-bytes 4)
                (throw 'done nil)))
          ;; body: decode length and consume the body
          (let* ((msg-len (ajnc--decode-header ajnc--recv-header))
                 (decoded-cnt (string-bytes ajnc--recv-body))
                 (need (- msg-len decoded-cnt)))
            (if (> need remaining)
                ;; partial body: keep available and stop
                (progn
                  (setq ajnc--recv-body
                        (concat ajnc--recv-body
                                (substring s pos)))
                  (throw 'done nil))
              ;; enough input to complete message
              (let ((body (substring s pos (+ pos need))))
                (setq pos (+ pos need))
                (setq remaining (- remaining need))
                (setq ajnc--recv-header "")
                (setq hdr-bytes 0)
                (setq ajnc--recv-body
                      (if (string-empty-p ajnc--recv-body)
                          body
                        (concat ajnc--recv-body body)))
                (push ajnc--recv-body completed)
                (setq ajnc--recv-body "")
                (when (= remaining 0)
                  ;; input consumed exactly at a message boundary
                  (setq boundary-stop t)
                  (throw 'done nil))))))))
    (if boundary-stop
        (nreverse completed)
      (when completed
        (setq ajnc--recv-held (nreverse completed)))
      nil)))

(defun ajnc--parse-concat (in-bytes)
  "Concatenation of every complete message parsed from IN-BYTES.
Returns \"\" if no complete messages are available."
  (let ((msgs (ajnc--parse in-bytes)))
    (if msgs (mapconcat #'identity msgs "") "")))


;;; Completion

(defcustom ajnc-completion-extra-words
  '("def" "defn" "defmacro" "undef" "var" "set" "let" "if" "fn")
  "A list of words offered as completion targets.
Used by `ajnc-completion-at-point' and collected from identifiers in the
interaction and REPL buffers. The netrepl protocol does not provide
server-side completion, so all completion needs to be done client-side."
  :type '(repeat string)
  :group 'ajnc)

(defcustom ajnc-completion-collect-expr
  "(keys (all-bindings))"
  "Janet expression evaluated to collect global bindings.
The `ajnc-collect-completions' evaluates `(all-bindings)' in the running
janet session and adds the binding names to `ajnc-completion-extra-words'."
  :type 'string
  :group 'ajnc)

(defconst ajnc--ident-regexp
  "\\(?:[A-Za-z_*+<>=!?/$%][A-Za-z0-9_*/+<>=!?&$%-]*\\)"
  "Identifier regexp used to gather local completion words.")

(defconst ajnc--ident-chars
  '(?_ ?* ?+ ?- ?< ?> ?= ?! ?? ?/ ?& ?$ ?% ?:)
  "Non-alphanumeric characters that can appear in identifiers.")

(defconst ajnc--complete-token-regexp
  (concat ":?" ajnc--ident-regexp)
  "Regexp matching a Janet identifier, optionally keyword-prefixed.")

(defvar-local ajnc--words-cache nil
  "Cached completion words per local buffer.")

(defvar-local ajnc--completion-request nil
  "Non-nil while `ajnc-collect-completions' awaits a result.
The next matching result from the filter is parsed as binding names
rather than ordinary output.")

(defun ajnc--buffer-words (buffer)
  "Return identifiers and keywords found in BUFFER as a list.
Cached per buffer, keyed by `buffer-chars-modified-tick'."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (let* ((tick (buffer-chars-modified-tick))
             (cached (and ajnc--words-cache
                          (eq (car ajnc--words-cache) tick)
                          (cdr ajnc--words-cache))))
        (or cached
            (let (words)
              (save-excursion
                (goto-char (point-min))
                (while (re-search-forward ajnc--ident-regexp nil t)
                  (push (match-string-no-properties 0) words)))
              (setq ajnc--words-cache (cons tick words))
              words))))))

(defun ajnc-completion-at-point ()
  "Completion function for netrepl REPL and interaction buffers.
Returns a `completion-at-point' entry for identifier at point, or nil.
Should be compatible with other completion packages using c-a-p.
Candidates are taken from the current buffer, the REPL buffer, and the
current janet environment via `ajnc-completion-extra-words'."
  (let* ((pos (point))
         (line-beg (line-beginning-position))
         (beg pos))
    (save-excursion
      (goto-char pos)
      (while (and (> (point) line-beg)
                  (let ((c (char-before)))
                    (or (and (<= ?a c) (<= c ?z))
                        (and (<= ?A c) (<= c ?Z))
                        (and (<= ?0 c) (<= c ?9))
                        (memq c ajnc--ident-chars))))
        (backward-char))
      (setq beg (point)))
    (when (and (> pos beg)
               (not (get-text-property beg 'read-only)))
      (let* ((repl-buffer (get-buffer (ajnc--repl-buffer-name-for
                                       (current-buffer))))
             (cands (delete-dups
                     (append (ajnc--buffer-words (current-buffer))
                             (unless (eq repl-buffer (current-buffer))
                               (ajnc--buffer-words repl-buffer))
                             ajnc-completion-extra-words)))
             (table (completion-table-with-cache
                     (lambda (str) (all-completions str cands)))))
        (list beg pos table :exclusive 'no)))))

(defun ajnc--completion-result-words (msg)
  "Extract completion words from a netrepl MSG."
  (let ((words '()))
    (when (and (string-prefix-p "(true " msg)
               (string-suffix-p ")" msg))
      (let ((body (substring msg 6 (1- (length msg))))
            (pos 0))
        (while (string-match ajnc--complete-token-regexp body pos)
          (push (match-string 0 body) words)
          (setq pos (match-end 0)))))
    (delete-dups words)))

(defun ajnc--populate-completions (words)
  "Merge WORDS into `ajnc-completion-extra-words'."
  (setq ajnc-completion-extra-words
        (sort (delete-dups (append ajnc-completion-extra-words words))
              #'string-lessp)))

;;;###autoload
(defun ajnc-collect-completions ()
  "Add completion targets from the current session.
Populate `ajnc-completion-extra-words' from global bindings by
evaluating `ajnc-completion-collect-expr' (via immediate-eval)."
  (interactive)
  (let ((repl-buffer (ajnc--repl-buffer)))
    (unless repl-buffer
      (error "Ajnc: no repl buffer for `%s'"
             (ajnc--repl-buffer-name-for (current-buffer))))
    (with-current-buffer repl-buffer
      (setq ajnc--completion-request t))
    (ajnc-send-immediate-code ajnc-completion-collect-expr)))


;;; Incoming message handling

(defvar-local ajnc--banner nil
  "Banner text shown in the REPL buffer before the first prompt.")

(defvar-local ajnc--pending-results 0
  "Number of outstanding immediate-eval requests (protocol step 4).")

(defun ajnc--result-p (msg)
  "Return non-nil if MSG is a netrepl evaluation result (protocol step 4)."
  (or (string-prefix-p "(true " msg)
      (string-prefix-p "(false " msg)))

(defun ajnc--prompt-p (msg)
  "Return non-nil if MSG looks like a netrepl repl prompt.
Prompt should have the form \"<client-name>:<line>:<state> \"."
  (string-prefix-p (format "%s:" ajnc-client-name) msg))

(defun ajnc--face-result (msg)
  "Return MSG annotated with result face."
  (put-text-property 0 (length msg) 'font-lock-face
                     'ajnc-repl-result-face msg) msg)

(defun ajnc--stream-buffer ()
  "Return the stream-output buffer (or create if necessary)."
  (or (get-buffer ajnc-stream-output-buffer-name)
      (with-current-buffer (get-buffer-create ajnc-stream-output-buffer-name)
        (buffer-disable-undo)
        (setq-local buffer-read-only nil)
        (current-buffer))))


(defun ajnc--stream-write (body)
  "Append streamed output BODY to the stream buffer.
When `ajnc-colorize-output' is non-nil BODY uses `font-lock-face' properties
from `ajnc--colorize' and is inserted unchanged. Otherwise, assume BODY is plain
text and the `ajnc-stream-face' is used."
  (unless (string-empty-p body)
    (unless ajnc-colorize-output
      (set-text-properties 0
                           (length body)
                           '(font-lock-face ajnc-stream-face)
                           body))
    (let ((buf (ajnc--stream-buffer)))
      (with-current-buffer buf
        (let ((inhibit-read-only t))
          (goto-char (point-max))
          (insert body)
          (unless (eq (char-before) ?\n)
            (insert "\n")))))))

(defun ajnc--filter (string)
  "Pre-output filter for netrepl STRING.
Dispatches 0xFF prefixed as streamed output, 0xFE as control data, responses
as results, and anything else as a repl prompt."
  (when ajnc--debug
    (message "received (hex): %S\nreceived (str): %s"
             (ajnc--hexstring string) string))
  (let* ((msgs (ajnc--parse string))
         (parts '())
         (prompt nil))
    (dolist (msg msgs)
      (let ((mlen (string-bytes msg))
            (res (ajnc--result-p msg)))
        (cond
         ;; streamed output
         ((and (> mlen 0) (= (aref msg 0) #xFF))
          (let ((shown (ajnc--display-body (substring msg 1))))
            (if ajnc-split-stream-output
                (ajnc--stream-write shown)
              (push shown parts))))
         ;; protocol control: discard 0xFE, process the rest
         ((and (> mlen 0) (= (aref msg 0) #xFE))
          (push (substring msg 1) parts))
         ;; result, or any outstanding reply that is not a prompt
         ((or res
              (and (> ajnc--pending-results 0)
                   (not (ajnc--prompt-p msg))))
          (when (> ajnc--pending-results 0)
            (setq ajnc--pending-results
                  (1- ajnc--pending-results)))
          (when (and ajnc--completion-request res)
            (setq ajnc--completion-request nil)
            (ajnc--populate-completions
             (ajnc--completion-result-words msg)))
          (push (ajnc--face-result msg) parts))
         ;; otherwise it's the repl prompt (?)
         ((> mlen 0)
          (setq prompt msg)
          (if ajnc--banner
              ;; banner appears once, before the first prompt
              (let ((banner ajnc--banner))
                (setq ajnc--banner nil)
                (push (concat banner "\n" msg) parts))
            (push msg parts))))))
    (when prompt
      ;; save the prompt for comint to apply properties
      (setq-local comint-prompt-regexp (regexp-quote prompt))
      (when ajnc--debug
        (message "prompt: %S" prompt)))
    (cond
     ((null parts) "")
     ((cdr parts) (apply #'concat (nreverse parts)))
     (t (car parts)))))


;;; ANSI color rendering

(defconst ajnc--term-faces
  [term-color-black term-color-red term-color-green term-color-yellow
                    term-color-blue term-color-magenta term-color-cyan term-color-white
                    term-color-bright-black term-color-bright-red term-color-bright-green
                    term-color-bright-yellow term-color-bright-blue term-color-bright-magenta
                    term-color-bright-cyan term-color-bright-white]
  "`term-color-*' faces indexed by ANSI color code 0..15.")

(defconst ajnc--ansi-rest
  (list :fg nil :bg nil :bold nil :faint nil :italic nil
        :underline nil :reverse nil)
  "Fresh SGR state. All attributes off, no foreground or background.")

(defvar-local ajnc--ansi-context nil
  "SGR context carried between calls to `ajnc--colorize'.
A list of (STATE FRAGMENT) or nil. STATE is the SGR plist active after the
previous input, FRAGMENT is any trailing partial escape.")

(defconst ajnc--csi-regexp "\e\\[[\x30-\x3F]*[\x20-\x2F]*[\x40-\x7E]"
  "Regexp matching a complete ANSI CSI sequence.")

(defconst ajnc--csi-fragment-regexp "\e\\[[\x30-\x3F]*[\x20-\x2F]*\\|\e"
  "Regexp matching an CSI prefix, or stray ESC.")

(defun ajnc--skip-csi (s i n)
  "Return the first index after a CSI sequence starting at I (an ESC) in S (len N)."
  (setq i (1+ i))
  (when (and (< i n) (= (aref s i) ?\[))
    (setq i (1+ i))
    (while (and (< i n)
                (let ((c (aref s i)))
                  (or (and (<= ?\s c) (<= c ?/))
                      (and (<= ?0 c) (<= c ??)))))
      (setq i (1+ i)))
    (when (and (< i n)
               (let ((c (aref s i)))
                 (and (<= ?@ c) (<= c ?~))))
      (setq i (1+ i))))
  i)

(defun ajnc--strip-ansi (s)
  "Return S with any ANSI escape sequences removed."
  (if (not (string-match-p "\e" s))
      s
    (let ((out '())
          (start 0)
          (i 0)
          (n (length s)))
      (while (< i n)
        (if (= (aref s i) ?\e)
            (progn
              (push (substring s start i) out)
              (setq i (ajnc--skip-csi s i n))
              (setq start i))
          (setq i (1+ i))))
      (when (> i start)
        (push (substring s start i) out))
      (apply #'concat (nreverse out)))))

(defun ajnc--ansi-face-for (code)
  "Return the `term-color-*' face for ANSI color CODE (0..15)."
  (aref ajnc--term-faces code))

(defun ajnc--ansi-fg-color (code)
  "Return the foreground color string for ANSI Color CODE via its term face."
  (face-foreground (ajnc--ansi-face-for code) nil 'default))

(defun ajnc--ansi-bg-color (code)
  "Return the background color string for ANSI Color CODE via its term face."
  (face-background (ajnc--ansi-face-for code) nil 'default))

(defun ajnc--ansi-256-color (code)
  "Return ANSI 256-color CODE (16..255) as hex.
16-231 is the 6x6x6 cube, 232-255 a 24-step gray ramp."
  (if (>= code 232)
      (let ((v (+ 8 (* 10 (- code 232)))))
        (format "#%02X%02X%02X" v v v))
    (let* ((c (- code 16))
           (r (/ c 36)) (g (% (/ c 6) 6)) (b (% c 6)))
      (format "#%02X%02X%02X"
              (min 255 (ajnc--cube-level r))
              (min 255 (ajnc--cube-level g))
              (min 255 (ajnc--cube-level b))))))

(defun ajnc--cube-level (level)
  "Return the RGB shaft level for cube coordinate LEVEL (0..5)."
  (if (zerop level) 0 (+ 40 (* level 55))))

(defun ajnc--ansi-set-color (state kind code)
  "Set STATE `:fg' or `:bg' (KIND) to ANSI Color CODE (0..15)."
  (plist-put state (if (eq kind 'fg) :fg :bg) code))

(defun ajnc--ansi-extended (state color params index)
  "Apply the extended color sequence at INDEX of PARAMS.
COLOR is `:fg' or `:bg'. Returns (STATE . NEXT-INDEX)."
  (let* ((mode (nth (1+ index) params))
         (next (+ index (cond ((= mode 5) 3)
                          ((= mode 2) 6)
                          (t 1))))
         (value (cond ((= mode 5)
                       (let ((code (nth (+ 2 index) params)))
                         (if (< code 16)
                             (aref ajnc--term-faces code)
                           (ajnc--ansi-256-color code))))
                      ((= mode 2)
                       (format "#%02X%02X%02X"
                               (or (nth (+ 2 index) params) 0)
                               (or (nth (+ 3 index) params) 0)
                               (or (nth (+ 4 index) params) 0))))))
    (cons (if value (plist-put state color value) state) next)))

(defun ajnc--ansi-apply-sgr (state params)
  "Update SGR STATE from numeric PARAMS.
Extended `38/48;5;N' and `38/48;2;R;G;B' are translated to `:fg' or `:bg'."
  (let ((i 0) (n (length params)))
    (while (< i n)
      (let* ((p (nth i params))
             (next (1+ i)))
        (cond
         ;; SGR reset
         ((= p 0)
          (setq state (copy-sequence ajnc--ansi-rest)))
         ;; attributes
         ((= p 1) (plist-put state :bold t))
         ((= p 2) (plist-put state :faint t))
         ((= p 3) (plist-put state :italic t))
         ((= p 4) (plist-put state :underline t))
         ((= p 7) (plist-put state :reverse t))
         ((= p 21) (plist-put state :bold nil))
         ((= p 22) (plist-put state :bold nil) (plist-put state :faint nil))
         ((= p 23) (plist-put state :italic nil))
         ((= p 24) (plist-put state :underline nil))
         ((= p 27) (plist-put state :reverse nil))
         ;; foreground
         ((<= 30 p 37) (setq state (ajnc--ansi-set-color state 'fg (- p 30))))
         ((<= 90 p 97) (setq state (ajnc--ansi-set-color state 'fg (+ 8 (- p 90)))))
         ;; background
         ((<= 40 p 47) (setq state (ajnc--ansi-set-color state 'bg (- p 40))))
         ((<= 100 p 107) (setq state (ajnc--ansi-set-color state 'bg (+ 8 (- p 100)))))
         ;; extended foreground/background colors
         ((= p 38)
          (let* ((r (ajnc--ansi-extended state :fg params i)))
            (setq state (car r) next (cdr r))))
         ((= p 48)
          (let* ((r (ajnc--ansi-extended state :bg params i)))
            (setq state (car r) next (cdr r))))
         ;; reset foreground / background
         ((= p 39) (plist-put state :fg nil))
         ((= p 49) (plist-put state :bg nil)))
        (setq i next)))
    state))

(defun ajnc--ansi-face-render (state)
  "Return the face spec for SGR STATE, or nil."
  (let (spec)
    (let ((fg (plist-get state :fg))
          (bg (plist-get state :bg)))
      (when fg
        (setq spec (plist-put spec :foreground
                              (if (numberp fg) (ajnc--ansi-fg-color fg) fg))))
      (when bg
        (setq spec (plist-put spec :background
                              (if (numberp bg) (ajnc--ansi-bg-color bg) bg)))))
    (when (plist-get state :bold)
      (setq spec (plist-put spec :weight 'bold)))
    (when (plist-get state :faint)
      (setq spec (plist-put spec :height 0.9)))
    (when (plist-get state :italic)
      (setq spec (plist-put spec :slant 'italic)))
    (when (plist-get state :underline)
      (setq spec (plist-put spec :underline t)))
    (when (plist-get state :reverse)
      (setq spec (plist-put spec :inverse-video t)))
    spec))

(defun ajnc--ansi-sgr-params (seq)
  "Return the numeric SGR parameters of completed escape SEQ."
  (let ((body (substring seq 2 (1- (length seq)))))
    (mapcar (lambda (f) (string-to-number f))
            (split-string body ";"))))

(defun ajnc--faceize (run state)
  "Return RUN propertyized with the face for SGR STATE."
  (let ((face (ajnc--ansi-face-render state)))
    (when (and face (not (string-empty-p run)))
      (put-text-property 0 (length run) 'font-lock-face face run))
    run))

(defun ajnc--colorize (string)
  "Return STRING with ANSI SGR escapes translated to faces.
16-color codes map to `term-color-*' faces (`ajnc--term-faces'), 256-color and
truecolor map to \"#RRGGBB\". The running SGR state and any trailing partial
escape are carried across calls by `ajnc--ansi-context'."
  (let ((ctx ajnc--ansi-context))
    (if (and (not (string-match-p "\e" string))
             (not (cadr ctx))
             (let ((s (car ctx)))
               (or (null s) (equal s ajnc--ansi-rest))))
        string
      (let* ((state (or (car ctx) (copy-sequence ajnc--ansi-rest)))
             (input (if (cadr ctx) (concat (cadr ctx) string) string))
             (n (length input))
             (frag nil)
             (out '())
             (pos 0))
        (setq ajnc--ansi-context nil)
        ;; Walk input, splitting it into plain-text runs at each escape.
        ;; The run ahead of a complete SGR escape takes the new state;
        ;; non-SGR CSIs and stray escapes are dropped.
        (while (< pos n)
          (if (not (string-match "\e" input pos))
              (setq out (cons (ajnc--faceize (substring input pos n) state) out)
                    pos n)
            (let* ((esc (match-beginning 0))
                   (run (ajnc--faceize (substring input pos esc) state)))
              (setq out (cons run out))
              (if (and (string-match ajnc--csi-regexp input esc)
                       (= (match-beginning 0) esc))
                  ;; complete CSI: only SGR (`m') changes the state
                  (if (= (aref input (1- (match-end 0))) ?m)
                      (setq state (ajnc--ansi-apply-sgr
                                   state (ajnc--ansi-sgr-params
                                          (substring input esc (match-end 0))))
                            pos (match-end 0))
                    (setq pos (match-end 0)))
                ;; no complete CSI: hold a tail that could continue
                ;; in the next message, or drop it
                (if (and (string-match ajnc--csi-fragment-regexp input esc)
                         (= (match-beginning 0) esc))
                    (let ((fx (match-end 0)))
                      (if (= fx n)
                          (setq frag (substring input esc) pos n)
                        (setq pos fx)))
                  (setq pos (1+ esc)))))))
        (setq ajnc--ansi-context (list state frag))
        (apply #'concat (nreverse out))))))

(defun ajnc--display-body (body)
  "Return streamed-output BODY prepared for display."
  (if ajnc-colorize-output
      (ajnc--colorize body)
    (ajnc--strip-ansi body)))


;;; NETREPL Protocol
;;

;;  1. server <- {connection settings, including client name} <- client
;;     1.1. If msg starts with 0xFF, parse message as (-> msg (slice 1) parse)
;;          and extract the :name key as the name. Other connection settings
;;          can be stored here.
;;     1.2. If msg does not start with 0xFF, the message is treated as the
;;          client name. Other options are considered nil.

;;  2. server -> {repl prompt (no newline)} -> client
;;
;;  3. server <- {one chunk of input (msg)} <- client
;;
;;  4. If (= (msg 0) 0xFF)
;;     4.1. (def result (-> msg (slice 1) parse eval protect))
;;     4.2. server -> result -> client
;;     4.3. goto 3

;;  5. If (= (msg 0) 0xFE)
;;     5.1. Return msg as either:
;;         - a keyword if the msg contains a command (e.g. :cancel)
;;         - an array if the msg contains a command and arguments
;;           (e.g. @[:source "path/to/source"]
;;     5.2. goto 6.2
;;
;;  6. Otherwise
;;     6.1. Send chunk to repl input stream
;;     6.1. Unless auto-flush is enabled,
;;         server -> {(dyn :out) and (dyn :err) (empty at first)} -> client
;;     6.3. goto 2
;;
;; via https://janet-lang.org/spork/api/netrepl.html

;; Protocol step 1

(defun ajnc--send-process (proc payload)
  "Length-prefix, debug-log, and send PAYLOAD to process PROC."
  (let ((msg (ajnc--frame payload)))
    (when ajnc--debug
      (message "sending: %S" msg))
    (process-send-string proc msg)))

(defun ajnc-send-hello (process hello-str)
  "Send PROCESS the HELLO-STR as connection settings.
A 0xFF-led Janet table sets the client :name and :auto-flush,
enabling streamed partial results."
  (ajnc--send-process process
                      (format "\xFF{:auto-flush true :name %S}" hello-str)))


;; Protocol step 2,3

(defun ajnc--send-to-repl (text)
  "Send TEXT through the repl input stream bound to the current buffer.
Reports a missing REPL buffer instead of raising an error."
  (let ((repl-buffer (ajnc--repl-buffer)))
    (if (not repl-buffer)
        (message "%s is missing..."
                 (ajnc--repl-buffer-name-for (current-buffer)))
      (with-current-buffer repl-buffer
        (goto-char (point-max))
        (insert text)
        (comint-send-input)))))

;;;###autoload
(defun ajnc-send-code (code-str)
  "Send CODE-STR, a Janet form, through the repl input stream."
  (interactive "sCode: ")
  (ajnc--send-to-repl code-str))

(defun ajnc--repl-process ()
  "Return the live repl process bound to the current buffer, else signal an error."
  (let ((proc (get-buffer-process (ajnc--repl-buffer))))
    (unless (and proc (process-live-p proc))
      (error "Ajnc: no live repl process (buffer `%s' missing?)"
             (ajnc--repl-buffer-name-for (current-buffer))))
    proc))

(defun ajnc--send-payload (payload)
  "Length-prefix and send PAYLOAD to the repl process."
  (ajnc--send-process (ajnc--repl-process) payload))


;; Protocol step 4

;;;###autoload
(defun ajnc-send-immediate-code (code-str)
  "Eval CODE-STR immediately on the server (protocol step 4)."
  (interactive "sImmediate code: ")
  (let ((repl-buffer (ajnc--repl-buffer)))
    (unless repl-buffer
      (error "Ajnc: buffer `%s' is missing"
             (ajnc--repl-buffer-name-for (current-buffer))))
    (ajnc--send-payload (concat "\xFF" code-str))
    ;; count the request only once it has actually been sent.
    ;; a failed send should not leave pending count raised
    (with-current-buffer repl-buffer
      (setq ajnc--pending-results
            (1+ ajnc--pending-results)))))


;; protocol step 5

;;;###autoload
(defun ajnc-send-command (command-str)
  "Send COMMAND-STR to the server (protocol step 5), 0xFE-prefixed.
Pass a BARE command name (\"cancel\", not \":cancel\"); the server
keyword-izes it and strips the 0xFE byte."
  (interactive "sCommand: ")
  (ajnc--send-payload (concat "\xFE" command-str)))

;;;###autoload
(defun ajnc-cancel ()
  "Send the cancel command to the netrepl server (protocol step 5).
Cancels the current evaluation, or is a no-op while idle."
  (interactive)
  (ajnc-send-command "cancel"))


;; Region and buffer sending

(defun ajnc-send-region (start end)
  "Send the selected region (START to END) to the netrepl REPL."
  (interactive "r")
  (ajnc--send-to-repl (buffer-substring-no-properties start end)))

(defun ajnc-send-buffer ()
  "Send buffer content."
  (interactive)
  (ajnc-send-region (point-min) (point-max)))

(defun ajnc-send-expression-at-point ()
  "Send expression at point."
  (interactive)
  (let* ((bound (bounds-of-thing-at-point 'sexp))
         (start (car bound))
         (end (cdr bound)))
    (when (and start end)
      (ajnc-send-region start end))))

;;;###autoload
(defun ajnc-switch-to-repl ()
  "Switch to the repl buffer bound to the current buffer."
  (interactive)
  (pop-to-buffer (ajnc--repl-buffer-name-for (current-buffer))))


;;; Modes and keymaps

(defvar ajnc-mode-map
  (let ((map (copy-keymap comint-mode-map)))
    (define-key map (kbd "<tab>")    #'completion-at-point)
    (define-key map (kbd "<down>")   #'comint-next-input)
    (define-key map (kbd "<up>")     #'comint-previous-input)
    (define-key map (kbd "C-c C-k")  #'ajnc-send-immediate-code)
    (define-key map (kbd "C-c C-q")  #'ajnc-stop-repl)
    (define-key map (kbd "C-c C-x")  #'ajnc-cancel)
    (easy-menu-define ajnc-mode-menu map
      "A Janet (Spork) Netrepl Client Mode Menu"
      '("Ajnc"
        ["Start REPL" ajnc-start-repl t]
        ["Send immediate eval" ajnc-send-immediate-code t]
        ["Cancel" ajnc-cancel t]
        ["Stop server" ajnc-stop-repl t]
        "--"
        ["Switch to other window" other-window t]))
    map)
  "Keymap for `ajnc-mode'.")


(define-derived-mode ajnc-mode comint-mode "Ajnc"
  "Major mode for ajnc, a Janet (Spork) Netrepl client REPL.

With `ajnc-mode' you can evaluate Janet forms in a netrepl server
as if they were typed at a REPL prompt:

  * Type a form and press RET to evaluate it (comint input).
  * \[ajnc-send-immediate-code] evaluates code directly, without
    updating the shared repl input stream.
  * \[ajnc-cancel] cancels the currently running evaluation.
  * Use <up> / <down> to walk the input history.
  * <tab> completes identifier at point.

\\{ajnc-mode-map}"
  :syntax-table lisp-mode-syntax-table
  (setq comint-prompt-read-only t)
  (add-hook 'comint-preoutput-filter-functions #'ajnc--filter nil 'local)
  (setq-local completion-at-point-functions
              '(ajnc-completion-at-point comint-completion-at-point))
  (setq comint-input-sender
        (lambda (proc string)
          (ajnc--send-process proc (concat string "\n"))))
  (setq mode-line-process '(":%s")))

(defvar ajnc-interaction-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-b") #'ajnc-send-buffer)
    (define-key map (kbd "C-c C-e") #'ajnc-send-expression-at-point)
    (define-key map (kbd "C-c C-r") #'ajnc-send-region)
    (define-key map (kbd "C-c C-z") #'ajnc-switch-to-repl)
    (define-key map (kbd "C-c C-s") #'ajnc-start-repl)
    (define-key map (kbd "C-c C-n") #'ajnc-start-new-repl)
    (define-key map (kbd "C-c C-9") #'ajnc-send-immediate-code)
    (define-key map (kbd "C-c C-x") #'ajnc-cancel)
    (define-key map (kbd "M-C-i")   #'completion-at-point)
    (easy-menu-define ajnc-interaction-mode-menu map
      "A Janet (Spork) Netrepl Client Interaction Mode Menu"
      '("Ajnc"
        ["Start REPL" ajnc-start-repl t]
        ["Start New REPL" ajnc-start-new-repl t]
        ["Send buffer" ajnc-send-buffer t]
        ["Send expression at point" ajnc-send-expression-at-point t]
        ["Send immediate eval" ajnc-send-immediate-code t]
        ["Cancel" ajnc-cancel t]
        "--"
        ["Send region" ajnc-send-region t]
        ["Switch to REPL" ajnc-switch-to-repl t]))
    map)
  "Keymap for `ajnc-interaction-mode'.")

;;;###autoload
(define-minor-mode ajnc-interaction-mode
  "Minor mode for ajnc interaction from a Janet buffer.

The following keys are available in `ajnc-interaction-mode':

\\{ajnc-interaction-mode-map}."
  :init-value nil
  :lighter " ajnc"
  :keymap ajnc-interaction-mode-map)


;;; Process sentinel

;;;###autoload
(defun ajnc-sentinel (process event)
  "Sentinel for the REPL PROCESS. EVENT is the usual sentinel event string."
  (when ajnc--debug
    (message "ajnc sentinel: %S" event))
  (cond ((string-prefix-p "connection broken by remote peer" event)
         (message "Ajnc: connection to netrepl server closed")
         (ajnc--recv-reset))
        ((string-prefix-p "open" event)
         (message "Ajnc: connected"))
        ((string-prefix-p "deleted" event)
         (message "Ajnc: process buffer deleted: %S" process)
         (ajnc--recv-reset))
        (t
         (message "Ajnc: process event: %S" event)
         (message "Ajnc: process: %S" process))))


;;; Connecting to a REPL

(defun ajnc--split-endpoint (endpoint)
  "Split ENDPOINT (\"host:port\") into (HOST PORT-STRING).
Only the first two colon-separated fields are used. Hostnames and IPv4
addresses can be used, IPv6 addresses are not (yet) supported."
  (let ((ep (split-string endpoint ":")))
    (list (car ep) (cadr ep))))

(defun ajnc--read-endpoint ()
  "Prompt for a netrepl endpoint, defaulting to `ajnc-default-endpoint'."
  (let ((endpoint ajnc-default-endpoint))
    (read-string (format "REPL endpoint (default '%s'): " endpoint)
                 endpoint nil endpoint)))


;;;###autoload
(defun ajnc (endpoint)
  "Start the ajnc REPL and connect to netrepl ENDPOINT (\"hostname:port\")."
  (interactive (list (ajnc--read-endpoint)))
  (ajnc--connect endpoint))

;;;###autoload
(defun ajnc-repl-connect (endpoint)
  "Connect the REPL to a running netrepl server ENDPOINT."
  (interactive (list (ajnc--read-endpoint)))
  (ajnc--connect endpoint))

(defun ajnc--connect (endpoint &optional proc-name buf-name)
  "Connect the REPL to a netrepl server at ENDPOINT.
The optional args PROC-NAME and BUF-NAME name a process and buffer
so several REPLs can coexist (on separate fibers)."
  (let* ((proc-name (or proc-name ajnc-repl-process-name))
         (buf-name (or buf-name ajnc-repl-buffer-name))
         (ep (ajnc--split-endpoint endpoint))
         (host (car ep))
         (port (string-to-number (cadr ep))))
    (when (and (null host) (<= port 0))
      (error "Invalid endpoint: %S" endpoint))
    (with-temp-message (format "Connecting to REPL on '%s:%d'..."
                               host port)
      ;; Get rid of a stale REPL process, if any.
      (let ((old-proc (get-buffer-process (get-buffer buf-name))))
        (when (and old-proc (process-live-p old-proc))
          (delete-process old-proc)))
      (let ((original-buffer (current-buffer))
            (proc-buffer (make-comint-in-buffer proc-name
                                                buf-name (cons host port))))
        (unless proc-buffer
          (error "Failed to connect to %s:%d" host port))
        (let ((repl-process (get-buffer-process proc-buffer))
              (repl-buffer (get-buffer buf-name)))
          (unless (and repl-process repl-buffer)
            (error "Failed to set up REPL process"))
          (set-process-sentinel repl-process #'ajnc-sentinel)
          (set-process-coding-system repl-process 'binary)
          (with-current-buffer repl-buffer
            (ajnc-mode)
            (setq ajnc--pending-results 0)
            (setq-local ajnc--ansi-context nil)
            (setq ajnc-repl-buffer (current-buffer))
            (setq-local ajnc-repl-port port)
            (setq ajnc--banner (format ";; connected to %s:%d" host port)))
          (ajnc--recv-reset)
          (ajnc-send-hello repl-process ajnc-client-name)
          (pop-to-buffer proc-buffer)
          (goto-char (point-max))
          (pop-to-buffer original-buffer)
          repl-buffer)))))


;;; Netrepl server lifecycle

(defun ajnc--server-args (host port)
  "Return (PROGRAM ARGS...) used to start a netrepl server on HOST:PORT."
  (let* ((cmd (string-replace "%p" (number-to-string port)
                              (string-replace "%h" host
                                              ajnc-netrepl-server-command)))
         (parts (split-string-and-unquote cmd)))
    (cond ((executable-find (car parts))
           parts)
          ((and (executable-find "janet")
                (string= ajnc-netrepl-server-command
                         "janet-netrepl -H %h -P %p"))
           (let ((script (make-temp-file "ajnc-netrepl-server-" nil ".janet")))
             (with-current-buffer (generate-new-buffer "*temporal disturbance*")
               (unwind-protect
                   (progn
                     (insert (format "(import spork/netrepl)
(netrepl/server %S %S)
(print \"ajnc-netrepl-ready\")
(flush)\n"
                                     host (number-to-string port)))
                     (write-region (point-min) (point-max) script))
                 (kill-buffer)))
             (list "janet" script)))
          (t
           (error "The netrepl server command was not found: %S"
                  ajnc-netrepl-server-command)))))


(defun ajnc--start-server (host port &optional proc-name buf-name)
  "Start a netrepl server process on HOST:PORT.
If optional args PROC-NAME and BUF-NAME are given, use them instead of
`ajnc-netrepl-server-process-name' and `ajnc-netrepl-server-buffer-name'
so that multiple servers can coexist. Returns the server process."
  (let* ((proc-name (or proc-name ajnc-netrepl-server-process-name))
         (buf-name (or buf-name ajnc-netrepl-server-buffer-name)))
    (with-current-buffer (get-buffer-create buf-name)
      (setq buffer-read-only nil)
      (erase-buffer)
      (setq-local mode-name "ajnc"))
    (apply #'start-process proc-name buf-name
           (ajnc--server-args host port))))

(defun ajnc--free-port (host)
  "Return a currently unused TCP port on HOST."
  (let ((server (make-network-process
                 :name "ajnc-netrepl-port-probe"
                 :server t :host host
                 :service "0" :noquery t)))
    (unwind-protect
        (let* ((contact (process-contact server :local)))
          (if (consp contact)
              (cdr contact)
            (aref contact (1- (length contact)))))
      (delete-process server))))

(defun ajnc--port-open-p (host port timeout)
  "Return non-nil if a TCP connection to HOST:PORT succeeds within TIMEOUT seconds."
  (let ((deadline (+ (float-time) timeout)))
    (catch 'open
      (while (< (float-time) deadline)
        (let* ((stream (open-network-stream "ajnc-netrepl-probe" nil host port
                                            :noquery t :nowait t))
               (count 0))
          (while (and (eq (process-status stream) 'connect) (< count 20))
            (accept-process-output stream 0.05)
            (setq count (1+ count)))
          (let ((live (process-live-p stream)))
            (delete-process stream)
            (when live (throw 'open t))))
        (sleep-for 0.05))
      nil)))

(defun ajnc--reported-port ()
  "Return the port a netrepl server printed in its startup output, or nil."
  (let ((buffer (get-buffer ajnc-netrepl-server-buffer-name)))
    (and buffer
         (with-current-buffer buffer
           (save-excursion
             (goto-char (point-min))
             (when (re-search-forward "port +\\([0-9]+\\)" nil t)
               (string-to-number (match-string 1))))))))

(defun ajnc--wait-server (process host port)
  "Wait for server PROCESS to listen on HOST:PORT.
Returns non-nil (waits up to `ajnc-start-timeout' seconds), or nil on failure."
  (let ((deadline (+ (float-time) ajnc-start-timeout)))
    (while (and (process-live-p process)
                (< (float-time) deadline)
                (not (ajnc--port-open-p host port 0.5))))
    (and (process-live-p process)
         (ajnc--port-open-p host port 1))))

(defun ajnc--launch-server (host)
  "Start a netrepl server process on HOST with next free port.
Waits for running server to report the port it is using and returns
a \"host:port\" endpoint. Retries with a new port if startup fails."
  (let ((attempt 0)
        (endpoint nil))
    (while (and (null endpoint) (< attempt 4))
      (setq attempt (1+ attempt))
      (let* ((port (ajnc--free-port host))
             (process (ajnc--start-server host port)))
        (if (ajnc--wait-server process host port)
            (let ((reported (ajnc--reported-port)))
              (setq endpoint (format "%s:%d" host
                                     (if (and reported (> reported 0))
                                         reported
                                       port))))
          (message "Ajnc: netrepl server failed to start (attempt %d); retrying..."
                   attempt)
          (when (process-live-p process)
            (delete-process process)))))
    (unless endpoint
      (error "Failed to start the netrepl server"))
    (message "Ajnc: netrepl server listening on '%s'" endpoint)
    endpoint))

;;;###autoload
(defun ajnc-start-repl ()
  "Start a Janet netrepl server and connect to it.

The server is launched on a free port using `ajnc-netrepl-server-command'
and runs in the buffer named by `ajnc-netrepl-server-buffer-name'.
Once the server reports the port it is using, `ajnc' connects to that endpoint."
  (interactive)
  (let ((host (car (ajnc--split-endpoint ajnc-default-endpoint))))
    (ajnc (ajnc--launch-server host))))

;;;###autoload
(defun ajnc-stop-repl ()
  "Stop the netrepl server process, if any."
  (interactive)
  (let ((process (get-process ajnc-netrepl-server-process-name)))
    (if (and process (process-live-p process))
        (progn
          (delete-process process)
          (message "Ajnc: stopped the netrepl server"))
      (message "Ajnc: no netrepl server is running"))))

(defun ajnc--current-repl-port ()
  "Return the port of the netrepl REPL bound to the current buffer."
  (or (let ((buf (ajnc--repl-buffer)))
        (when buf
          (buffer-local-value 'ajnc-repl-port buf)))
      (ajnc--reported-port)
      (error "Ajnc: no running netrepl REPL. Start one with `ajnc-start-repl' first")))


;;;###autoload
(defun ajnc-start-new-repl ()
  "Start an additional netrepl REPL."
  (interactive)
  (let* ((host (car (ajnc--split-endpoint ajnc-default-endpoint)))
         (port (ajnc--current-repl-port))
         (next-port (1+ port))
         (proc-name (format "ajnc-repl-process-%d" next-port))
         (buf-name (format "*janet-repl-%d*" next-port))
         (server-name (format "janet-netrepl-server-%d" next-port))
         (server-buf-name (format "*ajnc-server-%d*" next-port)))
    (when (get-process proc-name)
      (error "Ajnc: a REPL process named `%s' already exists" proc-name))
    (when (get-buffer-process (get-buffer buf-name))
      (error "Ajnc: a live process already exists in buffer `%s'" buf-name))
    (let* ((server (ajnc--start-server host next-port
                                       server-name server-buf-name))
           (original (current-buffer)))
      (unless (ajnc--wait-server server host next-port)
        (when (process-live-p server)
          (delete-process server))
        (error "Ajnc: netrepl server failed to start on port %d" next-port))
      (let ((repl (ajnc--connect (format "%s:%d" host next-port)
                                 proc-name buf-name)))
        (with-current-buffer original
          (setq-local ajnc-repl-buffer repl))
        (message "Ajnc: started REPL `%s' on port %d, linked to buffer `%s'"
                 buf-name next-port (buffer-name original))
        repl))))


(provide 'ajnc)

;;; ajnc.el ends here

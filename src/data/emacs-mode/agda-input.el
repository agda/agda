;;; agda-input.el --- The Agda input method -*- lexical-binding: t; -*-

;; SPDX-License-Identifier: MIT License

;;; Commentary:

;; A highly customisable input method which can inherit from other
;; Quail input methods.  By default the input method is geared towards
;; the input of mathematical and other symbols in Agda programs.
;;
;; Use M-x customize-group agda-input to customise this input method.
;; Note that the functions defined under "Functions used to tweak
;; translation pairs" below can be used to tweak both the key
;; translations inherited from other input methods as well as the
;; ones added specifically for this one.
;;
;; Use agda-input-show-translations to see all the characters which
;; can be typed using this input method (except for those
;; corresponding to ASCII characters).

;;; Code:

(require 'quail)
(require 'cl-lib)
;; Quail is quite stateful, so be careful when editing this code.  Note
;; that with-temp-buffer is used below whenever buffer-local state is
;; modified.

(unless (fboundp 'mapcan)
  (defun mapcan (func sequence)
    "Apply FUNC to each element of SEQUENCE.
Concatenate the results by altering them (using `nconc').
SEQUENCE may be a list, a vector, a boolean vector, or a string."
    (apply #'nconc (mapcar func sequence))))

(eval-and-compile
  (defun agda-input-to-string-list (s)
    "Convert a string S to a list of one-character strings.
Spaces and newlines are ignored."
    (declare (pure t))
    (let (list)
      (dotimes (i (length s))
        (let ((sub (substring s i (1+ i))))
          (unless (string-match-p "[[:space:]]" sub)
            (push sub list))))
      (nreverse list))))

(defun agda-input-character-range (from to)
  "A string consisting of the characters from FROM to TO."
  (let (seq)
    (dotimes (i (1+ (- to from)))
      (setq seq (cons (+ from i) seq)))
    (concat (nreverse seq))))

;;;; Functions used to tweak translation pairs
(defun agda-input-compose (f g)
  "Apply G before calling `agda-input-concat-map' with F."
  (lambda (x) (mapcan f (funcall g x))))

(defun agda-input-or (&rest fns)
  "Return a function that will apply and contact the results of FNS."
  (lambda (x)
    (apply #'append (mapcar (lambda (fn) (funcall fn x)) fns))))

(defun agda-input-nonempty ()
  "Only keep pairs with a non-empty first component."
  (lambda (x) (if (> (length (car x)) 0) (list x))))

(defun agda-input-prepend (prefix)
  "Prepend PREFIX to all key sequences."
  (lambda (x)
    (list (cons (concat prefix (car x)) (cdr x)))))

(defun agda-input-prefix (prefix)
  "Discard pairs where the key sequence doesn't start with PREFIX."
  (lambda (x)
    (and (string-prefix-p prefix (car x))
         (list x))))

(defun agda-input-suffix (suffix)
  "Only keep pairs whose key sequence ends with SUFFIX."
  (lambda (x)
    (and (string-suffix-p suffix (car x))
         (list x))))

(defun agda-input-drop (ss)
  "Drop pairs matching one of the given key sequences.
SS should be a list of strings."
  (lambda (x) (and (not (member (car x) ss)) (list x))))

(defun agda-input-drop-beginning (n)
  "Drop N characters from the beginning of each key sequence."
  (lambda (x)
    (list (cons (substring (car x) n) (cdr x)))))

(defun agda-input-drop-end (n)
  "Drop N characters from the end of each key sequence."
  (lambda (x)
    (list (cons (substring (car x) 0 (- (length (car x)) n))
                (cdr x)))))

(defun agda-input-drop-prefix (prefix)
  "Remove pairs that don't start with PREFIX.
This prefix is dropped."
  (agda-input-compose
   (agda-input-drop-beginning (length prefix))
   (agda-input-prefix prefix)))

(defun agda-input-drop-suffix (suffix)
  "Remove pairs that don't start with SUFFIX.
This suffix is dropped."
  (agda-input-compose
   (agda-input-drop-end (length suffix))
   (agda-input-suffix suffix)))

;;;; Functions to generate common ranges
(eval-and-compile
  (defun agda-input-common-range (input-fmt name-fmt mappings)
    "Generate a character range based on MAPPINGS.
MAPPINGS is an alist, mapping a input key to a part of a
character name.  E.g. `agda-input-greek-range' maps the \"α\" to
\"ALPHA\".  These are composed into entries adequat for
`agda-input-translations' or `agda-input-user-translations'.  To
construct these entries, INPUT-FMT and NAME-FMT are used.
INPUT-FMT is a format string (see `format') that will take the
key of each entry and apply it to the format string to get the
actual input method input (e.g. \"i%s\" if you want to map \iA
using `agda-input-latin-range').  NAME-FMT is used to construct
the unicode name of the sign.  You can find the name using
\\[execute-extended-command] `describe-char'.  This may
optionally also be a list, if you want to describe multiple
alternative mappings. This function is not meant to be used
directly, but via one of the wrapper functions
`agda-input-latin-range', `agda-input-greek-range',
`agda-input-number-range' or `agda-input-number-range*'."
    (let ((rules '()))
      (dolist (map mappings)
        (let ((assoc '()))
          (dolist (fmt name-fmt)
            (let ((char (char-from-name (format fmt (cdr map)))))
              (when char
                (push (string char) assoc))))
          (when assoc
            (push (cons (format input-fmt (car map))
                        (nreverse assoc))
                  rules))))
      (nreverse rules)))

  (defun agda-input-latin-range (input-fmt name-fmt &optional lower)
    "Create a mapping for latin characters.
If LOWER is non-nil, map lower case letters.  For details on
INPUT-FMT and NAME-FMT, see `agda-input-common-range'."
    (declare (pure t))
    (agda-input-common-range
     input-fmt (if (listp name-fmt) name-fmt (list name-fmt))
     (mapcar
      (lambda (c)
        (cons (string (if lower (downcase c) c)) (string c)))
      (number-sequence ?A ?Z))))

  (defun agda-input-greek-range (input-fmt name-fmt &optional lower)
    "Create a mapping for greek characters.
If LOWER is non-nil, map lower case letters.  For details on
INPUT-FMT and NAME-FMT, see `agda-input-common-range'."
    (declare (pure t))
    (agda-input-common-range
     input-fmt (list name-fmt)
     (mapcar
      (lambda (c)
        (cons (if lower (downcase (car c)) (car c)) (cdr c)))
      '(("A" . "ALPHA") ("B" . "BETA") ("G" . "GAMMA") ("D" . "DELTA")
        ("E" . "EPSILON") ("Z" . "ZETA") ("H" . "ETA") ("Th" . "THETA")
        ("I" . "IOTA") ("K" . "KAPPA") ("L" . "LAMBDA") ("M" . "MU")
        ("N" . "NU") ("X" . "XI") ("R" . "RHO") ("S" . "SIGMA")
        ("T" . "TAU") ("U" . "UPSILON") ("F" . "PHI") ("C" . "CHI")
        ("P" . "PSI") ("Pi" . "PI") ("P" . "PI") ("O" . "OMEGA")
        ("Omicron" . "OMICRON") ("X" . "XI") ("Z" . "ZETA")))))

  (defun agda-input-number-range (input-fmt &rest name-fmt)
    "Create a mapping for digits.
For details on INPUT-FMT and NAME-FMT, see
`agda-input-common-range'."
    (declare (pure t))
    (agda-input-common-range
     input-fmt name-fmt
     '(("0" . "ZERO") ("1" . "ONE") ("2" . "TWO") ("3" . "THREE")
       ("4" . "FOUR") ("5" . "FIVE") ("6" . "SIX") ("7" . "SEVEN")
       ("8" . "EIGHT") ("9" . "NINE") ("10" . "TEN"))))

  (defun agda-input-number-range* (input-fmt &rest name-fmt)
    "Create a mapping for numbers from 10 to 20.
For details on INPUT-FMT and NAME-FMT, see
`agda-input-common-range'."
    (declare (pure t))
    (agda-input-common-range
     input-fmt name-fmt
     '(("10" . "TEN") ("11" . "ELEVEN") ("12" . "TWELVE") ("13" . "THIRTEEN")
       ("14" . "FOURTEEN") ("15" . "FIFTEEN") ("16" . "SIXTEEN")
       ("17" . "SEVENTEEN") ("18" . "EIGHTEEN") ("19" . "NINETEEN")
       ("20" . "TWENTY")))))

;;;; Customization

;; The :set keyword is set to 'agda-input-incorporate-changed-setting
;; so that the input method gets updated immediately when users
;; customize it. However, the setup functions cannot be run before all
;; variables have been defined. Hence the :initialize keyword is set to
;; 'custom-initialize-default to ensure that the setup is not performed
;; until agda-input-setup is called at the end of this file.

(defgroup agda-input nil
  "The Agda input method.
After tweaking these settings you may want to inspect the resulting
translations using `agda-input-show-translations'."
  :group 'agda2
  :group 'leim)

(defcustom agda-input-tweak-all
  (agda-input-compose
   (agda-input-prepend "\\")
   (agda-input-nonempty))
  "Expression describing the transformations made upon the input mode.
The resulting function (if non-nil) is applied to every
\(KEY-SEQUENCE . TRANSLATION) pair and should return a list of such
pairs.  (Note that the translations can be anything accepted by
`quail-defrule'.)

If you change this setting manually (without using the
customization buffer) you need to call `agda-input-setup' in
order for the change to take effect."
  :group 'agda-input
  :set 'agda-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type 'sexp)

(defcustom agda-input-inherit
  `(("TeX" . ,(agda-input-compose
               (agda-input-drop '("geq" "leq" "bullet" "qed" "par"))
               (agda-input-or
                (agda-input-drop-prefix "\\")
                (agda-input-compose
                 (agda-input-drop '("^l" "^o" "^r" "^v"))
                 (agda-input-prefix "^"))
                (agda-input-prefix "_")))))
  "A list of Quail input methods for the Agda input mode.
Their translations should be inherited by the Agda input
method (with the exception of translations corresponding to ASCII
characters).

The list consists of pairs (qp . tweak), where qp is the name of
a Quail package, and tweak is an expression of the same kind as
`agda-input-tweak-all' which is used to tweak the translation
pairs of the input method.

The inherited translation pairs are added last, after
`agda-input-user-translations' and `agda-input-translations'.

If you change this setting manually (without using the
customization buffer) you need to call `agda-input-setup' in
order for the change to take effect."
  :group 'agda-input
  :set 'agda-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Quail package")
                       (sexp :tag "Tweaking function"))))

(defcustom agda-input-translations
  ;; The following list has been split into multiple smaller lists
  ;; to avoid triggering a stack overflow during evaluation, on
  ;; systems with a lower `max-lisp-eval-depth'.
  (append
;;;;; Equality and similar symbols.
   `(("eq" . ,(agda-input-to-string-list "=∼∽≈≋∻∾∿≀≃⋍≂≅ ≌≊≡≣≐≑≒≓≔≕≖≗≘≙≚≛≜≝≞≟≍≎≏≬⋕＝"))
     ("eqn" . ,(agda-input-to-string-list "≠≁ ≉     ≄  ≇≆  ≢                 ≭    "))

     ("=n"  . ("≠"))
     ("~"    . ,(agda-input-to-string-list "∼～"))
     ("~n"  . ("≁"))
     ("~~"   . ("≈"))  ("~~n" . ("≉"))
     ("~~~"  . ("≋"))
     (":~"   . ("∻"))
     ("~-"   . ("≃"))  ("~-n" . ("≄"))
     ("-~"   . ("≂"))
     ("~="   . ("≅"))  ("~=n" . ("≇"))
     ("~~-"  . ("≊"))
     ("=="   . ("≡"))  ("==n" . ("≢"))
     ("==="  . ("≣"))
     ("="    . ("＝"))
     (".="   . ("≐"))  (".=." . ("≑"))
     (":="   . ("≔"))  ("=:"  . ("≕"))
     ("=o"   . ("≗"))
     ("(="   . ("≘"))
     ("and=" . ("≙"))  ("or=" . ("≚"))
     ("*="   . ("≛"))
     ("t="   . ("≜"))
     ("def=" . ("≝"))
     ("m="   . ("≞"))
     ("?="   . ("≟")))

;;;;; Inequality and similar symbols.
   `(("leq"  . ,(agda-input-to-string-list "<≪⋘≤≦≲ ≶≺≼≾⊂⊆ ⋐⊏⊑ ⊰⊲⊴⋖⋚⋜⋞＜"))
     ("leqn" . ,(agda-input-to-string-list "≮  ≰≨≴⋦≸⊀ ⋨⊄⊈⊊  ⋢⋤ ⋪⋬   ⋠"))
     ("geq"  . ,(agda-input-to-string-list ">≫⋙≥≧≳ ≷≻≽≿⊃⊇ ⋑⊐⊒ ⊱⊳⊵⋗⋛⋝⋟＞"))
     ("geqn" . ,(agda-input-to-string-list "≯  ≱≩≵⋧≹⊁ ⋩⊅⊉⊋  ⋣⋥ ⋫⋭   ⋡"))

     ("<="   . ("≤"))  (">="   . ("≥"))
     ("<=n"  . ("≰"))  (">=n"  . ("≱"))
     ("len"  . ("≰"))  ("gen"  . ("≱"))
     ("<n"   . ("≮"))  (">n"   . ("≯"))
     ("<~"   . ("≲"))  (">~"   . ("≳"))
     ("<~n"  . ("⋦"))  (">~n"  . ("⋧"))
     ("<~nn" . ("≴"))  (">~nn" . ("≵"))

     ("sub"   . ("⊂"))  ("sup"   . ("⊃"))
     ("subn"  . ("⊄"))  ("supn"  . ("⊅"))
     ("sub="  . ("⊆"))  ("sup="  . ("⊇"))
     ("sub=n" . ("⊈"))  ("sup=n" . ("⊉"))

     ("squb"   . ("⊏"))  ("squp"   . ("⊐"))
     ("squb="  . ("⊑"))  ("squp="  . ("⊒"))
     ("squb=n" . ("⋢"))  ("squp=n" . ("⋣")))

;;;;; Set membership etc.
   `(("member" . ,(agda-input-to-string-list "∈∉∊∋∌∍⋲⋳⋴⋵⋶⋷⋸⋹⋺⋻⋼⋽⋾⋿"))

     ("inn" . ("∉"))
     ("nin" . ("∌")))

;;;;; Intersections, unions etc.
   `(("intersection" . ,(agda-input-to-string-list "∩⋂∧⋀⋏⨇⊓⨅⋒∏ ⊼      ⨉"))
     ("union"        . ,(agda-input-to-string-list "∪⋃∨⋁⋎⨈⊔⨆⋓∐⨿⊽⊻⊍⨃⊎⨄⊌∑⅀"))

     ("and" . ("∧"))  ("or"  . ("∨"))
     ("And" . ("⋀"))  ("Or"  . ("⋁"))
     ("i"   . ("∩"))  ("un"  . ("∪"))  ("u+" . ("⊎"))  ("u." . ("⊍"))
     ("I"   . ("⋂"))  ("Un"  . ("⋃"))  ("U+" . ("⨄"))  ("U." . ("⨃"))
     ("glb" . ("⊓"))  ("lub" . ("⊔"))
     ("Glb" . ("⨅"))  ("Lub" . ("⨆")))

;;;;; Entailment etc.
   `(("entails" . ,(agda-input-to-string-list "⊢⊣⊤⊥⊦⊧⊨⊩⊪⊫⊬⊭⊮⊯"))

     ("|-"   . ("⊢"))  ("|-n"  . ("⊬"))
     ("-|"   . ("⊣"))
     ("|="   . ("⊨"))  ("|=n"  . ("⊭"))
     ("||-"  . ("⊩"))  ("||-n" . ("⊮"))
     ("||="  . ("⊫"))  ("||=n" . ("⊯"))
     ("|||-" . ("⊪")))

;;;;; Divisibility, parallelity.
   `(("|"  . ("∣"))  ("|n"  . ("∤"))
     ("||" . ("∥"))  ("||n" . ("∦")))

;;;;; Some symbols from logic and set theory.
   `(("all" . ("∀"))
     ("ex"  . ("∃"))
     ("exn" . ("∄"))
     ("0"   . ("∅"))
     ("C"   . ("∁")))

;;;;; Corners, ceilings and floors.
   `(("c"  . ,(agda-input-to-string-list "⌜⌝⌞⌟⌈⌉⌊⌋"))
     ("cu" . ,(agda-input-to-string-list "⌜⌝  ⌈⌉  "))
     ("cl" . ,(agda-input-to-string-list "  ⌞⌟  ⌊⌋"))

     ("cul" . ("⌜"))  ("cuL" . ("⌈"))
     ("cur" . ("⌝"))  ("cuR" . ("⌉"))
     ("cll" . ("⌞"))  ("clL" . ("⌊"))
     ("clr" . ("⌟"))  ("clR" . ("⌋")))

;;;;; Various operators/symbols.
   `(("qed"       . ("∎"))
     ("x"         . ("×"))
     ("o"         . ("∘"))
     ("comp"      . ("∘"))
     ("."         . ,(agda-input-to-string-list "∙．"))
     ("*"         . ("⋆"))
     (".+"        . ("∔"))
     (".-"        . ("∸"))
     (":"         . ,(agda-input-to-string-list "∶⦂ː꞉˸፥፦：﹕︓"))
     (","         . ,(agda-input-to-string-list "ʻ،⸲⸴⹁⹉、︐︑﹐﹑，､"))
     (";"         . ,(agda-input-to-string-list "⨾⨟⁏፤꛶；︔﹔⍮⸵;"))
     ("::"        . ("∷"))
     ("::-"       . ("∺"))
     ("-:"        . ("∹"))
     ("+ "        . ("⊹"))
     ("+"         . ("＋"))
     ("sqrt"      . ("√"))
     ("surd3"     . ("∛"))
     ("surd4"     . ("∜"))
     ("increment" . ("∆"))
     ("inf"       . ("∞"))
     ("&"         . ("⅋"))
     ("z;"        . ,(agda-input-to-string-list "⨟⨾"))
     ("z:"        . ("⦂")))

;;;;; Circled operators.
   `(("o+"  . ("⊕"))
     ("o--" . ("⊖"))
     ("ox"  . ("⊗"))
     ("o/"  . ("⊘"))
     ("o."  . ("⊙"))
     ("oo"  . ("⊚"))
     ("o*"  . ("⊛"))
     ("o="  . ("⊜"))
     ("o-"  . ("⊝"))

     ("O+"  . ("⨁"))
     ("Ox"  . ("⨂"))
     ("O."  . ("⨀"))
     ("O*"  . ("⍟")))

;;;;; Boxed operators.
   `(("b+" . ("⊞"))
     ("b-" . ("⊟"))
     ("bx" . ("⊠"))
     ("b." . ("⊡")))

;;;;; Various symbols.
   `(("integral" . ,(agda-input-to-string-list "∫∬∭∮∯∰∱∲∳"))
     ("angle"    . ,(agda-input-to-string-list "∟∡∢⊾⊿"))
     ("join"     . ,(agda-input-to-string-list "⋈⋉⋊⋋⋌⨝⟕⟖⟗")))

  ("b+" . ("⊞"))
  ("b-" . ("⊟"))
  ("bx" . ("⊠"))
  ("b." . ("⊡"))

;;;;; APL boxed operators

  ("box="       . ("⌸"))
  ("box?"       . ("⍰"))
  ("box'"       . ("⍞"))
  ("box:"       . ("⍠"))
  ("box/"       . ("⍁"))
  ("box\\"      . ("⍂"))
  ("box<"       . ("⍃"))
  ("box>"       . ("⍄"))
  ("boxo"       . ("⌻"))
  ("boxO"       . ("⌼"))

  ("boxcomp"    . ("⌻"))
  ("boxcircle"  . ("⌼"))
  ("boxeq"      . ("⌸"))
  ("boxneq"     . ("⍯"))
  ("boxeqn"     . ("⍯"))

  ("boxl"       . ("⍇"))
  ("boxr"       . ("⍈"))
  ("boxu"       . ("⍐"))
  ("boxd"       . ("⍗"))

  ("boxdi"      . ("⌺"))
  ("boxdiv"     . ("⌹"))
  ("boxwedge"   . ("⍓"))
  ("boxvee"     . ("⍌"))
  ("boxdelta"   . ("⍍"))
  ("boxnabla"   . ("⍔"))

;;;;; Arrows.
   `(("l"  . ,(agda-input-to-string-list "←⇐⇚⭅⇇⇆↤⇦↞↼↽⇠⇺↜⇽⟵⟸↚⇍⇷ ↹     ↢↩↫⇋⇜⇤⟻⟽⤆↶↺⟲                                     "))
     ("r"  . ,(agda-input-to-string-list "→⇒⇛⭆⇉⇄↦⇨↠⇀⇁⇢⇻↝⇾⟶⟹↛⇏⇸⇶ ↴    ↣↪↬⇌⇝⇥⟼⟾⤇↷↻⟳⇰⇴⟴⟿ ➵➸➙➔➛➜➝➞➟➠➡➢➣➤➧➨➩➪➫➬➭➮➯➱➲➳➺➻➼➽➾⊸"))
     ("u"  . ,(agda-input-to-string-list "↑⇑⤊⟰⇈⇅↥⇧↟↿↾⇡⇞          ↰↱➦ ⇪⇫⇬⇭⇮⇯                                           "))
     ("d"  . ,(agda-input-to-string-list "↓⇓⤋⟱⇊⇵↧⇩↡⇃⇂⇣⇟         ↵↲↳➥ ↯                                                "))
     ("ud" . ,(agda-input-to-string-list "↕⇕   ↨⇳                                                                    "))
     ("lr" . ,(agda-input-to-string-list "↔⇔         ⇼↭⇿⟷⟺↮⇎⇹                                                        "))
     ("ul" . ,(agda-input-to-string-list "↖⇖                        ⇱↸                                               "))
     ("ur" . ,(agda-input-to-string-list "↗⇗                                         ➶➹➚                             "))
     ("dr" . ,(agda-input-to-string-list "↘⇘                        ⇲                ➴➷➘                             "))
     ("dl" . ,(agda-input-to-string-list "↙⇙                                                                         "))

     ("l-"  . ("←"))  ("<-"  . ("←"))  ("l="  . ("⇐"))  ("<="  . ("⇐"))
     ("r-"  . ("→"))  ("->"  . ("→"))  ("r="  . ("⇒"))  ("=>"  . ("⇒"))
     ("u-"  . ("↑"))                   ("u="  . ("⇑"))
     ("d-"  . ("↓"))                   ("d="  . ("⇓"))
     ("ud-" . ("↕"))                   ("ud=" . ("⇕"))
     ("lr-" . ("↔"))  ("<->" . ("↔"))  ("lr=" . ("⇔"))  ("<=>" . ("⇔"))
     ("ul-" . ("↖"))                   ("ul=" . ("⇖"))
     ("ur-" . ("↗"))                   ("ur=" . ("⇗"))
     ("dr-" . ("↘"))                   ("dr=" . ("⇘"))
     ("dl-" . ("↙"))                   ("dl=" . ("⇙"))

     ("l==" . ("⇚"))  ("l-2" . ("⇇"))                   ("l-r-" . ("⇆"))
     ("r==" . ("⇛"))  ("r-2" . ("⇉"))  ("r-3" . ("⇶"))  ("r-l-" . ("⇄"))
     ("u==" . ("⟰"))  ("u-2" . ("⇈"))                   ("u-d-" . ("⇅"))
     ("d==" . ("⟱"))  ("d-2" . ("⇊"))                   ("d-u-" . ("⇵"))

     ("l--"  . ("⟵"))  ("<--"  . ("⟵"))  ("l~"  . ("↜" "⇜"))
     ("r--"  . ("⟶"))  ("-->"  . ("⟶"))  ("r~"  . ("↝" "⇝" "⟿"))
     ("lr--" . ("⟷"))  ("<-->" . ("⟷"))  ("lr~" . ("↭"))

     ("l-n"  . ("↚"))  ("<-n"  . ("↚"))  ("l=n"  . ("⇍"))
     ("r-n"  . ("↛"))  ("->n"  . ("↛"))  ("r=n"  . ("⇏"))  ("=>n"  . ("⇏"))
     ("lr-n" . ("↮"))  ("<->n" . ("↮"))  ("lr=n" . ("⇎"))  ("<=>n" . ("⇎"))

     ("l-|"  . ("↤"))  ("ll-" . ("↞"))
     ("r-|"  . ("↦"))  ("rr-" . ("↠"))
     ("u-|"  . ("↥"))  ("uu-" . ("↟"))
     ("d-|"  . ("↧"))  ("dd-" . ("↡"))
     ("ud-|" . ("↨"))

     ("l->" . ("↢"))
     ("r->" . ("↣"))

     ("r-o" . ("⊸"))  ("-o"  . ("⊸"))

     ("dz" . ("↯")))

;;;;;; Ellipsis.
   `(("..." . ,(agda-input-to-string-list "⋯⋮⋰⋱")))

;;;;; Box-drawing characters.
   `(("---" . ,(agda-input-to-string-list "─│┌┐└┘├┤┬┼┴╴╵╶╷╭╮╯╰╱╲╳"))
     ("--=" . ,(agda-input-to-string-list "═║╔╗╚╝╠╣╦╬╩     ╒╕╘╛╞╡╤╪╧ ╓╖╙╜╟╢╥╫╨"))
     ("--_" . ,(agda-input-to-string-list "━┃┏┓┗┛┣┫┳╋┻╸╹╺╻
                                        ┍┯┑┕┷┙┝┿┥┎┰┒┖┸┚┠╂┨┞╀┦┟╁┧┢╈┪┡╇┩
                                        ┮┭┶┵┾┽┲┱┺┹╊╉╆╅╄╃ ╿╽╼╾"))
     ("--." . ,(agda-input-to-string-list "╌╎┄┆┈┊
                                        ╍╏┅┇┉┋")))

;;;;; Triangles (big/small, black/white)
   `(("t" . ,(agda-input-to-string-list "◂◃◄◅▸▹►▻▴▵▾▿◢◿◣◺◤◸◥◹"))
     ("T" . ,(agda-input-to-string-list "◀◁▶▷▲△▼▽◬◭◮"))

     ("tb" . ,(agda-input-to-string-list "◂▸▴▾◄►◢◣◤◥"))
     ("tw" . ,(agda-input-to-string-list "◃▹▵▿◅▻◿◺◸◹"))

     ("Tb" . ,(agda-input-to-string-list "◀▶▲▼"))
     ("Tw" . ,(agda-input-to-string-list "◁▷△▽")))

;;;;; Squares.
   `(("sq"  . ,(agda-input-to-string-list "■□◼◻◾◽▣▢▤▥▦▧▨▩◧◨◩◪◫◰◱◲◳"))
     ("sqb" . ,(agda-input-to-string-list "■◼◾"))
     ("sqw" . ,(agda-input-to-string-list "□◻◽"))
     ("sq." . ("▣"))
     ("sqo" . ("▢")))

;;;;; Rectangles.
   `(("re"  . ,(agda-input-to-string-list "▬▭▮▯"))
     ("reb" . ,(agda-input-to-string-list "▬▮"))
     ("rew" . ,(agda-input-to-string-list "▭▯")))

;;;;; Parallelograms.
   `(("pa"  . ,(agda-input-to-string-list "▰▱"))
     ("pab" . ("▰"))
     ("paw" . ("▱")))

;;;;; Diamonds.
   `(("di"  . ,(agda-input-to-string-list "◆◇◈"))
     ("dib" . ("◆"))
     ("diw" . ("◇"))
     ("di." . ("◈")))

;;;;; Circles.
   `(("ci"   . ,(agda-input-to-string-list "●○◎◌◯◍◐◑◒◓◔◕◖◗◠◡◴◵◶◷⚆⚇⚈⚉"))
     ("cib"  . ("●"))
     ("ciw"  . ("○"))
     ("ci."  . ("◎"))
     ("ci.." . ("◌"))
     ("ciO"  . ("◯")))

;;;;; Stars.
   `(("st"   . ,(agda-input-to-string-list "⋆✦✧✶✴✹ ★☆✪✫✯✰✵✷✸"))
     ("st4"  . ,(agda-input-to-string-list "✦✧"))
     ("st6"  . ("✶"))
     ("st8"  . ("✴"))
     ("st12" . ("✹")))

;;;;; Blackboard bold letters.
   (agda-input-latin-range "b%s" "DOUBLE-STRUCK CAPITAL %s")
   (agda-input-latin-range "b%s" "MATHEMATICAL DOUBLE-STRUCK CAPITAL %s")
   (agda-input-latin-range "b%s" "MATHEMATICAL DOUBLE-STRUCK SMALL %s" t)
   (agda-input-greek-range "bG%s" "DOUBLE-STRUCK CAPITAL %s")
   '(("bGS"  . ("⅀")))                  ;DOUBLE-STRUCK N-ARY SUMMATION
   (agda-input-greek-range "bG%s" "DOUBLE-STRUCK SMALL %s" t)

;;;;; Blackboard bold numbers.
   (agda-input-number-range "b%s" "MATHEMATICAL DOUBLE-STRUCK DIGIT %s")

;;;;; Mathematical bold letters.
   (agda-input-latin-range "B%s" "MATHEMATICAL BOLD CAPITAL %s")
   (agda-input-latin-range "B%s" "MATHEMATICAL BOLD SMALL %s" t)

;;;;; Mathematical bold Greek letters.
   (agda-input-greek-range "BG%s" "MATHEMATICAL BOLD CAPITAL %s")
   (agda-input-greek-range "BG%s" "MATHEMATICAL BOLD SMALL %s" t)
   '(("BOmicron" "𝚶")                   ;shorter alternatives (without "G")
     ("BPi" "𝚷")
     ("BGTH" "𝚯")
     ("Bomicron" "𝛐")
     ("Bpi" "𝛑")
     ("GTH" "Θ"))

;;;;; Mathematical bold digits.
   (agda-input-number-range "B%s" "MATHEMATICAL BOLD DIGIT %s")

;;;;; Fullwidth letters
   (agda-input-latin-range "F%s" "FULLWIDTH LATIN CAPITAL LETTER %s")
   (agda-input-latin-range "F%s" "FULLWIDTH LATIN SMALL LETTER %s" t)

;;;;; Fullwidth digits
   (agda-input-number-range "F%s" "FULLWIDTH DIGIT %s")

;;;;; Parentheses.
   `(("(" . ,(agda-input-to-string-list "([{⁅⁽₍〈⎴⟅⟦⟨⟪⦃〈《「『【〔〖〚︵︷︹︻︽︿﹁﹃﹙﹛﹝（［｛｢❪❬❰❲❴⟮⦅⦗⧼⸨❮⦇⦉"))
     (")" . ,(agda-input-to-string-list ")]}⁆⁾₎〉⎵⟆⟧⟩⟫⦄〉》」』】〕〗〛︶︸︺︼︾﹀﹂﹄﹚﹜﹞）］｝｣❫❭❱❳❵⟯⦆⦘⧽⸩❯⦈⦊"))

     ("[[" . ("⟦"))
     ("]]" . ("⟧"))
     ("<"  . ,(agda-input-to-string-list "⟨<≪⋘≺⊂⋐⊏⊰⊲⋖＜"))
     (">"  . ,(agda-input-to-string-list "⟩>≫⋙≻⊃⋑⊐⊱⊳⋗＞"))
     ("<<" . ("⟪"))
     (">>" . ("⟫"))
     ("{{" . ("⦃"))
     ("}}" . ("⦄"))

     ("(b" . ("⟅"))
     (")b" . ("⟆"))

     ("lbag" . ("⟅"))
     ("rbag" . ("⟆"))

     ("<|" . ("⦉"))  ;; Angle bar brackets
     ("|>" . ("⦊"))

     ("(|" . ("⦇"))  ;; Idiom brackets
     ("|)" . ("⦈"))

     ("((" . ,(agda-input-to-string-list "⦅｟"))  ;; Banana brackets
     ("))" . ,(agda-input-to-string-list "⦆｠")))

;;;;; Primes.
   `(("'" . ,(agda-input-to-string-list "′″‴⁗＇"))
     ("`" . ,(agda-input-to-string-list "‵‶‷｀")))

;;;;; Fractions.
   `(("frac" . ,(agda-input-to-string-list "¼½¾⅓⅔⅕⅖⅗⅘⅙⅚⅛⅜⅝⅞⅟")))

;;;;; Bullets.
   `(("bu"  . ,(agda-input-to-string-list "•◦‣⁌⁍"))
     ("bub" . ("•"))
     ("buw" . ("◦"))
     ("but" . ("‣")))

;;;;; Musical symbols.
   `(("note" . ,(agda-input-to-string-list "♩♪♫♬"))
     ("b"    . ("♭"))
     ("#"    . ("♯")))

;;;;; Other punctuation and symbols.
   `(("\\"         . ("\\"))
     ("en"         . ("–"))
     ("em"         . ("—"))
     ("!"          . ("！"))
     ("!!"         . ("‼"))
     ("?"          . ("？"))
     ("??"         . ("⁇"))
     ("?!"         . ("‽" "⁈"))
     ("!?"         . ("⁉"))
     ("die"        . ,(agda-input-to-string-list "⚀⚁⚂⚃⚄⚅"))
     ("asterisk"   . ,(agda-input-to-string-list "⁎⁑⁂✢✣✤✥✱✲✳✺✻✼✽❃❉❊❋＊"))
     ("8<"         . ("✂" "✄"))
     ("tie"        . ("⁀"))
     ("undertie"   . ("‿"))
     ("apl"        . ,(agda-input-to-string-list "⌶⌷⌸⌹⌺⌻⌼⌽⌾⌿⍀⍁⍂⍃⍄⍅⍆⍇⍈
                                               ⍉⍊⍋⍌⍍⍎⍏⍐⍑⍒⍓⍔⍕⍖⍗⍘⍙⍚⍛
                                               ⍜⍝⍞⍟⍠⍡⍢⍣⍤⍥⍦⍧⍨⍩⍪⍫⍬⍭⍮
                                               ⍯⍰⍱⍲⍳⍴⍵⍶⍷⍸⍹⍺⎕"))
     ("#"          . ("＃"))
     ("%"          . ("％"))
     ("&"          . ("＆"))
     ("*"          . ("＊"))
     ("/"          . ,(agda-input-to-string-list "／＼"))
     ("@"          . ("＠"))
     ("__"         . ("＿"))
     ("\""         . ("＂")))

;;;;; Some combining characters.

   ;; The following combining characters also have (other)
   ;; translations:
   ;; ̀ ́ ̂ ̃ ̄ ̆ ̇ ̈ ̋ ̌ ̣ ̧ ̱

   `(("^--" . ,(agda-input-to-string-list"̅̿"))
     ("_--" . ,(agda-input-to-string-list"̲̳"))
     ("^~"  . ,(agda-input-to-string-list"̃͌"))
     ("_~"  .  (                         "̰"))
     ("^."  . ,(agda-input-to-string-list"̇̈⃛⃜"))
     ("_."  . ,(agda-input-to-string-list"̣̤"))
     ("^l"  . ,(agda-input-to-string-list"⃖⃐⃔"))
     ("^l-" .  (                         "⃖"))
     ("^r"  . ,(agda-input-to-string-list"⃗⃑⃕"))
     ("^r-" .  (                         "⃗"))
     ("^lr" .  (                         "⃡"))
     ("_lr" .  (                         "͍"))
     ("^^"  . ,(agda-input-to-string-list"̂̑͆"))
     ("_^"  . ,(agda-input-to-string-list"̭̯̪"))
     ("^v"  . ,(agda-input-to-string-list"̌̆"))
     ("_v"  . ,(agda-input-to-string-list"̬̮̺")))

;;;;; Shorter forms of many greek letters plus ƛ.
   (agda-input-greek-range "G%s" "GREEK CAPITAL LETTER %s")
   (agda-input-greek-range "G%s" "GREEK SMALL LETTER %s" t)
   '(("Gl-" . ("ƛ")))                     ;LATIN SMALL LETTER LAMBDA WITH STROKE

;;;;; Mathematical characters
   '(("Mih" "ℎ"))                       ;PLANCK CONSTANT
   (agda-input-latin-range "Mi%s" "MATHEMATICAL ITALIC CAPITAL %s")
   (agda-input-latin-range "Mi%s" "MATHEMATICAL ITALIC SMALL %s" t)
   (agda-input-latin-range "MI%s" "MATHEMATICAL BOLD ITALIC CAPITAL %s")
   (agda-input-latin-range "MI%s" "MATHEMATICAL BOLD ITALIC SMALL %s" t)
   (agda-input-latin-range "Mc%s" "SCRIPT CAPITAL %s")
   (agda-input-latin-range "Mc%s" "MATHEMATICAL SCRIPT CAPITAL %s")
   (agda-input-latin-range "Mc%s" "SCRIPT SMALL %s" t)
   (agda-input-latin-range "Mc%s" "MATHEMATICAL SCRIPT SMALL %s" t)
   (agda-input-latin-range "MC%s" "MATHEMATICAL BOLD SCRIPT CAPITAL %s")
   (agda-input-latin-range "MC%s" "MATHEMATICAL BOLD SCRIPT SMALL %s" t)
   (agda-input-latin-range "Mf%s" "BLACK-LETTER CAPITAL %s")
   (agda-input-latin-range "Mf%s" "MATHEMATICAL FRAKTUR CAPITAL %s")
   (agda-input-latin-range "Mf%s" "MATHEMATICAL FRAKTUR SMALL %s" t)

;;;;; (Sub / Super) scripts

   ;; Unicode 12.1 omits several latin characters from sub/superscript.
   ;; https://www.quora.com/Why-is-there-no-character-for-superscript-q-in-Unicode
   ;;
   ;; Perhaps they will be added in future versions, however there
   ;; are no proposals for it currently in the pipeline:
   ;; https://www.unicode.org/alloc/Pipeline.html.  As soon as they
   ;; are avaliable `agda-input-latin-range' will generate them here:

   (agda-input-latin-range "_%s" "LATIN SUBSCRIPT CAPITAL LETTER %s")
   (agda-input-latin-range "_%s" "LATIN SUBSCRIPT SMALL LETTER %s" t)
   (agda-input-greek-range "_G%s" "GREEK SUBSCRIPT CAPITAL LETTER %s")
   (agda-input-greek-range "_G%s" "GREEK SUBSCRIPT SMALL LETTER %s" t)

   (agda-input-latin-range "^%s" "MODIFIER LETTER CAPITAL %s")
   (agda-input-latin-range "^%s" "MODIFIER LETTER SMALL %s" t)
   (agda-input-latin-range "^%s" "SUPERSCRIPT LATIN SMALL LETTER %s" t)
   (agda-input-greek-range "^G%s" "MODIFIER LETTER CAPITAL %s")
   (agda-input-greek-range "^G%s" "MODIFIER LETTER SMALL %s" t)
   '(("^Gg" "ᵞ")                        ;LETTER SMALL GREEK GAMMA
     ("^Ge" "ᵋ")                        ;MODIFIER LETTER SMALL OPEN E
     ("^Gf" "ᵠ")                        ;MODIFIER LETTER SMALL GREEK PHI
     )

;;;;; Some ISO8859-1 characters.
   `((" "         . (" "))
     ("!"         . ("¡"))
     ("cent"      . ("¢"))
     ("brokenbar" . ("¦"))
     ("degree"    . ("°"))
     ("?"         . ("¿"))
     ("^a_"       . ("ª"))
     ("^o_"       . ("º")))

;;;;; Circled, parenthesised etc. numbers and letters.
   (agda-input-number-range
    "(%s)"
    "PARENTHESIZED DIGIT %s"
    "CIRCLED DIGIT %s"
    "DIGIT %s FULL STOP"
    "NEGATIVE CIRCLED DIGIT %s"
    "DINGBAT NEGATIVE CIRCLED DIGIT %s"
    "DINGBAT CIRCLED SANS-SERIF DIGIT %s"
    "DINGBAT NEGATIVE CIRCLED SANS-SERIF DIGIT %s"
    )
   (agda-input-number-range*
    "(%s)"
    "PARENTHESIZED NUMBER %s"
    "CIRCLED NUMBER %s"
    "NUMBER %s FULL STOP"
    "DINGBAT NEGATIVE CIRCLED NUMBER %s"
    "DINGBAT CIRCLED SANS-SERIF NUMBER %s"
    "DINGBAT NEGATIVE CIRCLED SANS-SERIF NUMBER %s"
    "NEGATIVE CIRCLED NUMBER %s"
    )
   (agda-input-latin-range
    "(%s)"
    '("PARENTHESIZED LATIN SMALL LETTER %s"
      "CIRCLED LATIN CAPITAL LETTER %s"
      "CIRCLED LATIN SMALL LETTER %s"
      "NEGATIVE CIRCLED LATIN CAPITAL LETTER %s"
      "SQUARED LATIN CAPITAL LETTER %s"
      "NEGATIVE SQUARED LATIN CAPITAL LETTER %s")
    t))
  "A list of translations specific to the Agda input method.
Each element is a pair (KEY-SEQUENCE-STRING . LIST-OF-TRANSLATION-STRINGS).
All the translation strings are possible translations
of the given key sequence; if there is more than one you can choose
between them using the arrow keys.

Note that if you customize this setting you will not
automatically benefit (or suffer) from modifications to its
default value when the library is updated.  If you just want to
add some bindings it is probably a better idea to customize
`agda-input-user-translations'.

These translation pairs are included after those in
`agda-input-user-translations', but before the ones inherited
from other input methods (see `agda-input-inherit').

If you change this setting manually (without using the
customization buffer) you need to call `agda-input-setup' in
order for the change to take effect."
  :group 'agda-input
  :set #'agda-input-incorporate-changed-setting
  :initialize #'custom-initialize-default
  :type '(alist :key-type key-sequence
                :value-type (repeat :tag "Translations" string)))

(defcustom agda-input-user-translations nil
  "Additional user rules akin to `agda-input-translations'.

These translation pairs are included first, before those in
`agda-input-translations' and the ones inherited from other input
methods."
  :group 'agda-input
  :set #'agda-input-incorporate-changed-setting
  :initialize #'custom-initialize-default
  :type '(repeat (cons (string :tag "Key sequence")
                       (repeat :tag "Translations" string))))

;;;; Inspecting and modifying translation maps

(defun agda-input-get-translations (qp)
  "Return a list containing all translations from the Quail package QP.
Excepted are those that correspond to ASCII.  Each pair in the
list has the form (KEY-SEQUENCE . TRANSLATION)."
  (with-temp-buffer
    (activate-input-method qp) ; To make sure that the package is loaded.
    (unless (quail-package qp)
      (error "%s is not a Quail package" qp))
    (let ((decode-map (list 'decode-map)))
      (quail-build-decode-map (list (quail-map)) "" decode-map 0)
      (cdr decode-map))))

(defun agda-input-show-translations (qp)
  "Display all translations used by the Quail package QP (a string).
\(Except for those corresponding to ASCII)."
  (interactive (list (read-input-method-name
                      "Quail input method (default %s): " "Agda")))
  (let ((buf (concat "*" qp " input method translations*")))
    (with-output-to-temp-buffer buf
      (with-current-buffer buf
        (quail-insert-decode-map
         (cons 'decode-map (agda-input-get-translations qp)))))))

(defun agda-input-add-translations (trans)
  "Add the given translations TRANS to the Agda input method.
TRANS is a list of pairs (KEY-SEQUENCE . TRANSLATION).  The
translations are appended to the current translations."
  (with-temp-buffer
    (dolist (tr (mapcan agda-input-tweak-all trans))
      (quail-defrule (car tr) (cdr tr) "Agda" t))))

(defun agda-input-inherit-package (qp &optional fun)
  "Let the Agda input method inherit the translations from the Quail package QP.
Excepting those corresponding to ASCII.  The optional function
FUN can be used to modify the translations.  It is given a
pair (KEY-SEQUENCE . TRANSLATION) and should return a list of
such pairs."
  (let ((trans (agda-input-get-translations qp)))
    (agda-input-add-translations
     (if fun (mapcan fun trans) trans))))

;;;; Setting up the input method

(defun agda-input-setup ()
  "Set up the Agda input method."
  ;; Create (or reset) the input method.
  (with-temp-buffer
    (quail-define-package
     "Agda" "UTF-8" "∏" t ; guidance
     "Agda input method.
The purpose of this input method is to edit Agda programs, but
since it is highly customisable it can be made useful for other
tasks as well."
     nil nil nil nil nil nil t ; maximum-shortest
     ))

  (agda-input-add-translations
   (mapcar (lambda (tr) (cons (car tr) (vconcat (cdr tr))))
           (append agda-input-user-translations
                   agda-input-translations)))
  (dolist (def agda-input-inherit)
    (agda-input-inherit-package (car def) (cdr def))))

(defun agda-input-incorporate-changed-setting (sym val)
  "Update the Agda input method and set SYM to VAL.
This is done based on the customisable variables and underlying
input methods.  Suitable for use in the :set field of
`defcustom'."
  (set-default sym val)
  (agda-input-setup))

;; Set up the input method.

(agda-input-setup)

(provide 'agda-input)
;;; agda-input.el ends here

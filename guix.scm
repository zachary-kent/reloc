;; ReLoC -- Relational logic for fine-grained concurrency
;;
;; GNU Guix developement package
;; To build and install:
;;
;;     guix package -f guix.scm
;;
;; To build it without installing:
;;
;;     guix build -f guix.scm
;;
;; To use as the basis for a development environment, run:
;;
;;     guix environment -l guix.scm
;;

(define-module (coq)
  #:use-module (guix licenses)
  #:use-module (guix packages)
  #:use-module (guix build utils)
  #:use-module (guix build-system gnu)
  #:use-module (guix download)
  #:use-module (guix gexp)
  #:use-module (guix git-download)
  #:use-module (gnu packages base)
  #:use-module (gnu packages rsync)
  #:use-module (gnu packages python)
  #:use-module (gnu packages gawk)
  #:use-module (gnu packages ocaml)
  #:use-module (gnu packages coq)
  #:use-module ((guix licenses) #:prefix license:))

(define stdpp-commit "d6eb24f23eeb42529210a4d422392d7950d920c0")
(define stdpp-sha256 (base32 "1m1ys10f16v5ndxmwfjnw43p0qdb6fkk08z8864357zwmpvf2vgg")) ;; sha256 hash of the specific std++ checkout
(define iris-commit "a9031f7f4979974426c5c9fa4ac315863b99c362")
(define iris-sha256 (base32 "05kmbljc68ndnl8jyn3xy14f3vhcbxq7n2n3bkjyyfiyl8b2vaql")) ;; sha256 hash of the specific std++ checkout
(define %source-dir (dirname (current-filename)))

(define-public coq-stdpp
  (let ((branch "master")
        (commit stdpp-commit))
    (package
      (name "coq-stdpp")
      (synopsis "An alternative Coq standard library coq-std++")
      (version (git-version "dev" branch commit))
      (source (origin
               (method git-fetch)
               (uri (git-reference
                     (url "https://gitlab.mpi-sws.org/iris/stdpp.git")
                     (commit commit)))
               (file-name (git-file-name name version))
               (sha256 stdpp-sha256)))
      (build-system gnu-build-system)
      (native-inputs
       `( ;; need for egrep for tests
         ("grep" ,grep)
         ("gawk" ,gawk)
         ;; need diff for tests
         ("diffutils" ,diffutils)))
      (inputs
       `(("coq" ,coq)))
      (arguments
       `(#:tests? #f
         #:phases
         (modify-phases %standard-phases
           (delete 'configure)
           (replace 'install
             (lambda* (#:key outputs #:allow-other-keys)
               (setenv "COQLIB" (string-append (assoc-ref outputs "out") "/lib/coq/"))
               (zero? (system* "make"
                               (string-append "COQLIB=" (assoc-ref outputs "out")
                                              "/lib/coq/")
                               "install")))))))
      (description "This project contains an extended \"Standard Library\" for Coq called coq-std++.")
      (home-page "https://gitlab.mpi-sws.org/iris/stdpp")
      (license license:bsd-3))))

(define-public coq-iris
  (let ((branch "master")
        (commit iris-commit))
    (package
      (name "coq-iris")
      (synopsis "Higher-Order Concurrent Separation Logic Framework implemented and verified in the proof assistant Coq")
      (version (git-version "dev" branch commit))
      (source (origin
               (method git-fetch)
               (uri (git-reference
                     (url "https://gitlab.mpi-sws.org/iris/iris.git")
                     (commit commit)))
               (file-name (git-file-name name version))
               (sha256 iris-sha256)))
      (build-system gnu-build-system)
      (native-inputs
       `(;; need for egrep for tests
         ("grep" ,grep)
         ("gawk" ,gawk)
         ;; need diff for tests
         ("diffutils" ,diffutils)
         ("coq" ,coq)
         ("coq-stdpp" ,coq-stdpp)
         ("camlp5" ,camlp5)))
      (arguments
       `(#:tests? #f
         #:phases
         (modify-phases %standard-phases
           (delete 'configure)
           (replace 'install
             (lambda* (#:key outputs #:allow-other-keys)
               (setenv "COQLIB" (string-append (assoc-ref outputs "out") "/lib/coq/"))
               (invoke "make"
                       (string-append "COQLIB=" (assoc-ref outputs "out")
                                      "/lib/coq/")
                       "install"))))))
      (description "Iris Coq formalization")
      (home-page "https://gitlab.mpi-sws.org/iris/iris")
      (license license:bsd-3))))

(package
  (name "coq-reloc")
  (version "git")
  (source (local-file %source-dir
                      #:recursive? #t
                      #:select? (git-predicate %source-dir)))
  (build-system gnu-build-system)
  ;; We propogate all the inputs, because then it's just easier to set up the dev environment
  (propagated-inputs
   `(("coq"           ,coq)
     ("coq-autosubst" ,coq-autosubst)
     ("coq-stdpp"     ,coq-stdpp)
     ("coq-iris"      ,coq-iris)))
  (arguments
   `(#:phases
     (modify-phases %standard-phases
       (delete 'configure)
       (delete 'check)
       (replace 'install
         (lambda* (#:key outputs #:allow-other-keys)
           (setenv "COQLIB" (string-append (assoc-ref outputs "out") "/lib/coq/"))
           (invoke "make"
                   (string-append "COQLIB=" (assoc-ref outputs "out")
                                  "/lib/coq/")
                   "install"))))))  
  (home-page "https://cs.ru.nl/~dfrumin/reloc/")
  (synopsis "Relational logic for fine-grained concurrency")
  (description "ReLoC Coq formalization")
  (license license:bsd-3))

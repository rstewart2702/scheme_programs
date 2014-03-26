;; Attempting to develop web client software in Scheme to try and
;; retrieve important data, in Json form, from Jira servers?

;; (use-modules (web uri) (web client))

;; Turns out that the code shipped with guile 2.0.5, at least as packaged by
;; the doggone Lubuntu/Ubuntu stuff, is a screwed up mess, and doesn't
;; work as advertised.  Hard to understand that, but they have repaired it
;; by guile 2.0.9, which I have been able to build for both Linux and
;; Cygwin under Windoze.
;;
;; Don't know how to feel about that.  It sure makes it hard for a web
;; quasi-newbie like me to figure out what's going on, and makes the
;; "batteries included" claims of other language environments, like
;; Python and Ruby, ring pretty harshly in my ears.
;;
;; Fortunately, the library source and its change history being open to
;; inspection is ALWAYS a huge win in these situations, as well as the
;; relative simplicity of Scheme, even for what seem to be pretty
;; complicated tasks.

;; So, I shall have to try to get the revised stuff installed into my
;; Linux, and perhaps the updated package can be pushed into the Ubuntu
;; repositories?  Sheesh.

(use-modules (web uri) (web client) (web response) (web request) (web http))

(let
    ((my-uri (string->uri "http://rstewart-VirtualBox") ))
  (http-get my-uri #:port (open-socket-for-uri my-uri) )   )

(let
    ((my-uri (string->uri "http://www.google.com") ))
  (http-get my-uri #:port (open-socket-for-uri my-uri) )   )

(let*
    ((my-uri (string->uri "http://rstewart-virtualbox") )
     ;; (requester (lambda () (http-get my-uri #:keep-alive? #t)) )
     (requester (lambda () (http-get my-uri #:keep-alive? #f)) )
     ;; (requester (lambda () (http-get my-uri #:keep-alive? #t #:port (open-socket-for-uri my-uri))) )
     (receiver (lambda (header-junk body-junk) (list header-junk body-junk)))
     (result (call-with-values requester receiver))
     )
  (display (car result)) (display "\n")
  (display (cdr result)) (display "\n") )



(let*
    ((my-uri (string->uri "http://rstewart-VirtualBox:80"))
     (my-request (build-request my-uri))
     )
  (list (request-method my-request)
        (uri->string (request-uri my-request))
        (request-version my-request)
        (request-headers my-request)
        (request-meta my-request)
        (request-port my-request)) )

(let*
    ((my-uri (string->uri "http://www.google.com:80"))
     (my-request (build-request my-uri))
     )
  (list (request-method my-request)
        (uri->string (request-uri my-request))
        (request-version my-request)
        (request-headers my-request)
        (request-meta my-request)
        (request-port my-request)) )

(use-modules (ice-9 rdelim))

(let* (
       (ai (car (getaddrinfo "www.google.com" "http")) )
       (s (socket (addrinfo:fam ai) (addrinfo:socktype ai) (addrinfo:protocol ai)))
       )
  ;;(connect s AF_INET (inet-pton AF_INET "") 80)
  (connect s (addrinfo:addr ai))
  (display "GET / HTTP/1.0\r\n\r\n" s)

  (do ((line (read-line s) (read-line s)))
      ((eof-object? line))
    (display line)
    (newline)))

(let*
    ((my-uri (build-uri 'http #:host "www.google.com" #:port 80 #:path "/") )
     (req (build-request my-uri #:version '(1 . 1) ) )
     (port (open-socket-for-uri my-uri))
     )
  (write-request req port)
  (force-output port)
  (let*
      ((my-response (read-response port))
       (my-body (read-response-body my-response)) )
    (close-port port)
    (display my-response) (display "\n")
    (display my-body) (display "\n")
    ;; (close-port port)
    )
  )

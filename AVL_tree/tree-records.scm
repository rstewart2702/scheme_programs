(define tree-x
  (new-tree
   '(tree-rec "Stewart, Richard" (a b c))
   (lambda (x y) (string<? (cadr x) (cadr y))) ) )
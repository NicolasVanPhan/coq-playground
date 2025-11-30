
From Coq Require Extraction.
Extraction Language OCaml.

Require Import Chapter6.

(* Pick the constants you want to export *)
Extraction "mypred_strong2.ml" mypred_strong2.

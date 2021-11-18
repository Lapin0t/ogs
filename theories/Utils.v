From OGS.Utils Require Export Prelude Psh FFun.

(* TODO: move this somewhere else? *)
From ExtLib.Data Require Import Fin List.
From Equations Require Import Equations.
Set Equations Transparent.

Equations l_get {X} (xs : list X) : fin (length xs) -> X :=
  l_get (cons x xs) (F0)   := x ;
  l_get (cons x xs) (FS i) := l_get xs i .
Notation "xs .[ i ]" := (l_get xs i) (at level 30).

(*Dokaz algoritma insertion sort.*)

(*Knjižnice.*)
Require Import List.
Require Import Bool.
Require Import ZArith.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(*Funcija za insertion sort.*)
Fixpoint insertion_sort (l : list Z):= 
True.

(*Funkcija za urejen seznam.*)
Fixpoint urejen_seznam (l : list Z) := 
True.

(*Funkcija za permutiran seznam.*)
Fixpoint permutiran_seznam (l : list Z) := 
True.

(*Dokaz.*)
Theorem dokaz (l : list Z):
insertion_sort l -> urejen_seznam l /\ permutiran_seznam l.
Proof.
  admit.
Qed.
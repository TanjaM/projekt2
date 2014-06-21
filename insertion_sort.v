(*Dokaz algoritma insertion sort.*)

(*KNJIŽNICE*)
Require Import List.
Require Import Bool.
Require Import ZArith.
(*Notacija za sezname.*)
Local Open Scope list_scope.
Local Open Scope Z_scope.


(*-----   INSERTION SORT   -----*)
(*Vstavi trenutni element na pravo mesto v seznam.*)
Fixpoint vstavi_el (x : Z)(l : list Z) :=
  match l with
  | nil => x::nil
  | y::l' => 
    if Z.leb x y then x::l' else y::vstavi_el x l'
end.

(*Funcija za insertion sort.*)
Fixpoint insertion_sort (l : list Z) : list Z:= 
  match l with
  | nil => nil
  | x::l' => vstavi_el x (insertion_sort l')
end.


(*-----   UREJEN SEZNAM   -----*)
(*Funkcije za urejen seznam.*)
Fixpoint urejen_seznam (l : list Z) := 
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => x <= y /\ urejen_seznam l'
end.


(*-----   PERMUTIRAN SEZNAM   -----*)
(*Prešteje kolikokrat se pojavi trenutni element.*)
Fixpoint pojavi (x : Z) (l : list Z) : nat :=
  match l with
    | nil => O
    | y :: l' =>
      if x =? y then S (pojavi x l') else pojavi x l'
  end.

(*Funkcija, ki preveri ali je seznam permutiran.*)
Definition permutiran_seznam (l1 l2 : list Z) :=
  forall x : Z, pojavi x l1 = pojavi x l2.

(*Notacija za permutacijo*)
Notation "l1 ~~ l2" := (permutiran_seznam l1 l2) (at level 70).


(*-----    DOKAZ    -----*)
Theorem dokaz (l : list Z): urejen_seznam(insertion_sort l) /\ l ~~ (insertion_sort l).
Proof.
  admit.
Qed.







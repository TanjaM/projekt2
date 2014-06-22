(*Dokaz algoritma insertion sort.*)

(*KNJIŽNICE*)
Require Import List.
Require Import Bool.
Require Import ZArith.
(*Notacija za sezname.*)
Open Scope list_scope.
Open Scope Z_scope.

(*-----   INSERTION SORT   -----*)
(*Vstavi trenutni element na pravo mesto v seznam.*)
Fixpoint vstavi_el (x : Z)(l : list Z) {struct l }: list Z:=
  match l with
  | nil => x::nil
  | y::l' => 
    match Z_le_gt_dec x y with
      | left _ =>  x :: y :: l'
      | right _ => y :: (vstavi_el x l')
      end
end.

(*Funcija za insertion sort.*)
Fixpoint insertion_sort (l : list Z) : list Z:= 
  match l with
  | nil => nil
  | x::l' => vstavi_el x (insertion_sort l')
end.


(*-----   UREJEN SEZNAM   -----*)
(*Funkcija, ki preveri ali je seznam urejen.*)
Fixpoint urejen_seznam (l : list Z) := 
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => x <= y /\ urejen_seznam l'
end.


(*-----   PERMUTIRAN SEZNAM   -----*)
(*Prešteje kolikokrat se pojavi trenutni element.*)
Fixpoint pojavi (x : Z) (l : list Z){struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') =>
      match Z_eq_dec x z' with
      | left _ => S (pojavi x l')
      | right _ => pojavi x l'
      end
  end.

(*Funkcija, ki preveri ali je seznam permutiran.*)
Definition permutiran_seznam (l1 l2 : list Z) :=
  forall x : Z, pojavi x l1 = pojavi x l2.

(*Notacija za permutacijo*)
Notation "l1 ~~ l2" := (permutiran_seznam l1 l2) (at level 70).


(*-----    DOKAZ    -----*)

(*Pomožne leme za permutacijo*)

(*Prazen seznam*)
Lemma perm_nil : (permutiran_seznam(nil)(nil)).
Proof.
 intro z.
 simpl.
 auto.
Qed.

Lemma perm_list: forall (z:Z) (l l':list Z), permutiran_seznam l l' -> permutiran_seznam (z :: l) (z :: l').
Proof.
 intros z l l' H z'.
 simpl; case (Z_eq_dec z' z); auto.
Qed.

Lemma equiv_refl : forall l:list Z, permutiran_seznam l l.
Proof.
 unfold permutiran_seznam; trivial.
Qed.

Lemma equiv_sym : forall l l':list Z, permutiran_seznam l l' -> permutiran_seznam l' l.
Proof.
  unfold permutiran_seznam; auto.
Qed.

Lemma equiv_trans :
 forall l l' l'':list Z, permutiran_seznam l l' -> permutiran_seznam l' l'' -> permutiran_seznam l l''.
Proof.
 intros l l' l'' H H0 z.
 eapply trans_eq; eauto.
Qed.

Lemma perm :
 forall (a b:Z) (l l':list Z), permutiran_seznam l l' -> permutiran_seznam (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H z; simpl.
 case (Z_eq_dec z a); case (Z_eq_dec z b); 
 simpl; case (H z); auto.
Qed.

Lemma enaka: forall (l l' : list Z), l=l' -> l~~l'.
Proof.
 admit. 
Qed.

(*Pomožne leme za urejanost seznama.*)
(*vstavi_el x l mora imeti natako take elemente kot x::l*)
Lemma vstavi_el_enaka : forall (l:list Z) (x:Z), 
                  permutiran_seznam(x :: l)(vstavi_el x l).
Proof.
 induction l as [|a l0 H]; simpl ; auto.
 intros x.
 - apply perm_list.
   apply perm_nil.
 - intros x.
   case (Z_le_gt_dec x a); simpl; auto.
   + intros.
     apply perm_list.
     apply perm_list.
     apply enaka.
     auto.
   + 
     intro; apply equiv_trans with (a :: x :: l0); auto.
     * apply perm.
       apply enaka.
       auto.
     * apply perm_list.
       auto.
Qed.

(*po vstavljanju je seznam še vedno urejen*)
Lemma urejen_po_vstavljanju : forall (x : Z)(l : list Z), urejen_seznam l -> urejen_seznam((vstavi_el x l)).
Proof.
 (*induction l ;  simpl; auto.
 intro z.
 case (Z_le_gt_dec x z); simpl ; auto with zarith.
 intros z1 z2 ; case (Z_le_gt_dec x z2); simpl; intros.
 case (Z_le_gt_dec x z1); simpl; auto with zarith.
 case (Z_le_gt_dec x z1); simpl; auto with zarith.*)
 admit. (*DOKONČAJ!!!!*)
Qed.

(*Theorem dokaz (l : list Z): urejen_seznam(insertion_sort l) /\ l ~~ (insertion_sort l).
*)
Theorem dokaz : (l : (list Z)){l' : list Z | l~~l' /\ urejen_seznam l'}
Proof.
 intro l; induction l.
 exists (nil Z); split; auto.
 case Hrecl; intros l’ [H0 H1].
 exists (insert a l’).
 split.
 apply equiv_trans with (a::l’) ; auto.
 apply vstavi_el_enaka.
 apply urejen_po_vstavljanju  ; auto.
Qed.









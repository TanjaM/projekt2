(*Dokaz algoritma insertion sort.*)

(*KNJIŽNICE*)
Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Recdef.
(*Notacija za sezname.*)
Open Scope list_scope.
Open Scope Z_scope.

(*-----   INSERTION SORT   -----*)

(*Funkcija, ki vstavi trenutni element na pravo mesto v seznam.*)
Fixpoint vstavi (x : Z) (l : list Z) : list Z :=
  match l with
    | nil => x :: nil
    | y :: l' => if Z.leb x y
                 then x :: y :: l'
                 else y :: vstavi x l'
  end.

(*Funcija za insertion sort.*)
Fixpoint insertion_sort (l : list Z) : list Z:= 
  match l with
  | nil => nil
  | x::l' => vstavi x (insertion_sort l')
end.

(*-----   UREJEN SEZNAM   -----*)

(*Funkcija, ki preveri ali je seznam urejen.*)
Fixpoint urejen (l : list Z) :=
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => x <= y /\ urejen l'
  end.

Lemma urejen_tail(x : Z)(l:list Z): urejen(x::l)-> urejen l.
Proof.
 induction l; firstorder.
Qed.

(*-----   PERMUTIRAN SEZNAM   -----*)

(*Prešteje kolikokrat se pojavi iskani element.*)
Fixpoint pojavi (x : Z) (l : list Z) : nat :=
  match l with
    | nil => O
    | y :: l' => if x =? y then S (pojavi x l') else pojavi x l'
  end.

(*Definicija, ki pove kaj pomeni, da je l' permutacija l.*)
Definition permutiran_seznam (l l' : list Z) := 
  forall x : Z, pojavi x l = pojavi x l'.

(*Notacija za permutacijo.*)
Notation "l ~~ l'" := (permutiran_seznam l l')(at level 70).

(*-----    DOKAZ    -----*)

(*Pomožna lema za dokaz urejenosti.*)
Lemma urejen_po_vstavljanju (x : Z) (l : list Z): urejen l -> urejen (vstavi x l).
Proof.
  intro.
  induction l ; simpl; auto.
  case_eq (x <=? a)%Z.
    + intro G.
      simpl.
      split.
      *apply Zle_is_le_bool in G.
       auto.
      *apply H.
    + intro G.
      simpl.
      destruct l.
      * simpl.
        split.
        apply Z.lt_le_incl.
        apply Z.leb_gt in G.
        auto.
        auto.
      * simpl.
        apply Z.leb_gt in G.
        case_eq (x <=? z).
        - intro A.
          apply Z.leb_le in A.
          split; firstorder.
        - intro B.
          apply Z.leb_gt in B.
          split; firstorder.
          replace (z :: vstavi x l) with (vstavi x(z :: l)).
          apply H1.
          simpl.
          apply Z.leb_gt in B.
          rewrite B.
          reflexivity.
Qed.

(*Pomožna lema za dokaz permutacije.*)
Lemma vstavi_enak (x : Z) (l : list Z): pojavi x (vstavi x l) = S (pojavi x l).
Proof.
 induction l.
 - simpl; rewrite Z.eqb_refl; auto.
 - simpl; case_eq (x <=? a).
   + intro; simpl; rewrite Z.eqb_refl; auto.
   + intro; simpl; case (x =? a); auto.  
Qed.

(*Pomožna lema za dokaz permutacije.*)
Lemma vstavi_ni_enak (x y : Z) (l : list Z): (x =? y = false) -> pojavi x l = pojavi x (vstavi y l).
Proof.
  induction l.
  - intro; simpl; rewrite H; auto.
  - intro; simpl.
    case_eq (x =? a).
    + intro G.
      case_eq (y <=? a).
      * intro G1; simpl; rewrite H, G; auto.
      * intro G2; simpl; rewrite IHl, G; auto.   
    + intro G.
      case_eq (y <=? a).
      * intro G1; simpl; rewrite H, G; auto.
      * intro G2; simpl; rewrite IHl, G; auto.
Qed.

(*Dokazati moramo, da je seznam v insertion_sort permutiran vhodni seznam in da je urejen.*)
Theorem permutacija (l : list Z): l ~~ insertion_sort l.
Proof.
 induction l.
 - intro; auto.
 - intro; simpl.
   case_eq (x =? a).
   + intro; simpl.
     rewrite IHl.
     rewrite Z.eqb_eq in H.
     rewrite H.
     rewrite (vstavi_enak a (insertion_sort l)). 
     auto.
   + intro.
     rewrite IHl.
     rewrite (vstavi_ni_enak x a (insertion_sort l)).
     * auto.
     * apply H.
Qed. 

Theorem urejenost (l : list Z): urejen(insertion_sort l).
Proof.
 - induction l.
   + simpl; auto.
   + simpl.
     apply urejen_po_vstavljanju.
     simpl.
     auto.
Qed.
Require Import List PeanoNat Arith.

Open Scope nat_scope.
Require Import Permutation.
Require Import Sorted.

Print nat.
Print nat_ind.
Check nat_ind.

Inductive sorted : list nat -> Prop :=
| sorted_nil: sorted nil
| sorted_one: forall x, sorted (x :: nil)
| sorted_all: forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Fixpoint num_oc n l  :=
  match l with
    | nil => 0
    | h :: tl =>
      if n =? h then S(num_oc n tl) else  num_oc n tl 
  end.

Lemma num_oc_S: forall n l1 l2, num_oc n (l1 ++ n :: l2) = S (num_oc n (l1 ++ l2)).
Proof.
  induction l1.
  - intro l2.
    simpl.
    rewrite Nat.eqb_refl; reflexivity.
  - intro l2.
    simpl.
    destruct (n =? a); rewrite IHl1; reflexivity.
Qed.

Lemma num_oc_neq: forall n a l1 l2, n =? a = false -> num_oc n (l1 ++ a :: l2) = num_oc n (l1 ++ l2).
Proof.
  induction l1.
  - intros l2 H.
    simpl.
    rewrite H.
    reflexivity.
  - intros l2 Hfalse.
    simpl.
    destruct (n =? a0) eqn:H.
    + apply (IHl1 l2) in Hfalse.
      rewrite Hfalse; reflexivity.
    + apply (IHl1 l2) in Hfalse.
      assumption.
Qed.

Lemma num_oc_swap: forall l1 l2 n, num_oc n (l1 ++ l2) = num_oc n (l2 ++ l1).
Proof.
  induction l1.
  - intros l2 n.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  - intros l2 n.
    simpl.
    destruct (n =? a) eqn:H.
    + apply Nat.eqb_eq in H; subst.
      rewrite num_oc_S.
      rewrite IHl1.
      reflexivity.
    + rewrite num_oc_neq.
      * rewrite IHl1.
        reflexivity.
      * assumption.
Qed.

Definition equiv l l' := forall n:nat, num_oc n l = num_oc n l'. (**voltar pra x*)

Inductive perm: list nat -> list nat -> Prop :=
| perm_eq: forall l, perm l l
| perm_hd: forall x l l', perm l l' -> perm (x::l) (x::l')
| perm_swap: forall x y l l', perm l l' -> perm (x::y::l) (y::x::l')
| perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Lemma perm_app_cons: forall l1 l2 a, perm (a :: l1 ++ l2) (l1 ++ a :: l2).
Proof.
  induction l1.
  - intros l2 a.
    simpl.
    apply perm_eq.
  - intros l2 a'.
    simpl.
    apply perm_trans with (a :: a' :: l1 ++ l2).
    + apply perm_swap.
      apply perm_eq.
    + apply perm_hd.
      apply IHl1.
Qed.

Lemma perm_to_permutation: forall l l', perm l l' -> equiv l l'.
Proof.
  intros l l' H.
  unfold equiv.
  intro.
  induction H.
    - reflexivity.
    - simpl.
      destruct (n =? x).
      + rewrite IHperm.
        reflexivity.
      + assumption.
    - simpl.
      destruct (n =? y).
      + rewrite IHperm.
        destruct (n =? x).
        * reflexivity.
        * reflexivity.
      + destruct (n =? x).
        * rewrite IHperm.
          reflexivity.
        * assumption.
    - rewrite IHperm1.
      rewrite IHperm2.
      reflexivity.
Qed.

Lemma perm_equiv_Permutation: forall l1 l2, perm l1 l2 <-> Permutation l1 l2.
Proof.
Admitted.

Lemma perm_nil: forall l, equiv nil l -> l = nil.
Proof.
  intros l H.
  induction l.
  - reflexivity.
  - unfold equiv in H.
    assert(H' := H a).
    simpl in H'.
    rewrite Nat.eqb_refl in H'.
    discriminate.
Qed.

Lemma perm_sym: forall l l', equiv l l' -> equiv l' l.
Proof.
  intros l l' H.
  unfold equiv in *.
  intro n.
  apply eq_sym.
  apply H.
Qed.

Lemma perm_cons: forall n l l', equiv (n :: l) (n :: l') <-> equiv l l'.
Proof.
  intros n l l'; split.
  - intro H.
    unfold equiv in *.
    intro n'.
    assert (H' := H n').
    clear H.
    simpl in *.
    destruct (n' =? n).
    + inversion H'.
      reflexivity.
    + inversion H'.
      reflexivity.
  - intro H.
    unfold equiv in *.
    intro n'.
    simpl.
    destruct (n' =? n).
    + assert (H := H n').
      rewrite H.
      reflexivity.
    + apply H.
Qed.

Lemma permutation_trans: forall l1 l2 l3, equiv l1 l2 -> equiv l2 l3 -> equiv l1 l3.
Proof.
  intros.
  induction l1.
  -apply perm_nil in H.
   rewrite H in H0.
   assumption.
  -unfold equiv in *.
   simpl in *.
   intros n.
   assert (H := H n).
   destruct (n =? a) in *.
   + rewrite H.
     apply H0.
   + rewrite H.
     apply H0.
Qed.

Lemma perm_comm_app: forall l1 l2, equiv (l1 ++ l2) (l2 ++ l1).
Proof.
  intros l1 l2.
  unfold equiv.
  apply num_oc_swap.
Qed.


Lemma permutation_app_cons: forall l1 l2 a, equiv (l1 ++ a :: l2) (a :: l1 ++ l2).
Proof.
  induction l1.
          *** intros l2 a; simpl.
              unfold equiv.
              intro n; reflexivity.
          *** intros l2 a'.
              apply permutation_trans with  ((a' :: l2) ++ (a :: l1)).
              **** apply perm_comm_app.
              **** rewrite <- app_comm_cons.
                   apply perm_cons.
                   rewrite <- app_comm_cons.
                   apply perm_comm_app.
Qed.

Lemma perm_cons_num_oc: forall n l l', equiv (n :: l) l' -> exists x, num_oc  n l' = S x.
Proof.
  intros.
  unfold equiv in H.
  assert (Hn := H n).
  rewrite <- Hn.
  simpl.
  rewrite Nat.eqb_refl.
  exists (num_oc n l).
  reflexivity.
Qed.

Lemma num_occ_cons: forall l x n, num_oc x l = S n -> exists l1 l2, l = l1 ++ x :: l2 /\ num_oc x (l1 ++ l2) = n.
Proof.
  intros.
  induction l.
  - simpl in H.
    discriminate.
  - simpl in H.
    destruct (x =? a) eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      subst.
      exists nil.
      exists l.
      simpl.
      split.
      * reflexivity.
      * inversion H.
        reflexivity.
    + apply IHl in H.
      destruct H as [l1 [l2 [H1 H2]]].
      exists (a :: l1).
      exists l2.
      simpl.
      rewrite Heq.
      split.
      * rewrite H1.
        reflexivity.
      * rewrite H2.
        reflexivity.
Qed.

Lemma permutation_to_perm: forall l l', equiv l l' -> perm l l'.
Proof.
induction l.
- intros.
   apply perm_nil in H.
   subst.
   apply perm_eq.
- intros l' Hequiv.
   generalize dependent a.
   generalize dependent l.
   case l'.
   + intros.
     apply perm_sym in Hequiv.
     apply perm_nil in Hequiv.
     rewrite Hequiv.
     apply perm_eq.
   + intros a1 l1.
     intros.
     admit.
Admitted.

Theorem perm_equiv: forall l l', perm l l' <-> equiv l l'.
Proof.
  intros l l'.
  split.
  - apply perm_to_permutation.
  - apply permutation_to_perm.
Qed.

Fixpoint order (l : list nat) :=
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => x <= y /\ order l'
  end.

Lemma tail (x : nat) (l : list nat) :
  order (x :: l) -> order l.
Proof.
  induction l ; firstorder.
Qed.

Lemma head(x : nat) (l : list nat) :
  order (x :: l) -> forall y, In y l -> x <= y.
Proof.
  generalize x ; clear x.
  induction l.
  - simpl ; tauto.
  - intros x [H G] z [K|K].
    + now destruct K.
    + transitivity a ; auto.
Qed.

Lemma order_lt_cons (x : nat) (l : list nat) :
  (forall y : nat, In y l -> x <= y) -> order l -> order (x :: l).
Proof.
  intros H G.
  induction l ; [ simpl ; auto | idtac ].
  split.
  - apply H ; simpl ; auto.
  - destruct l ; simpl ; auto.
Qed.

Fixpoint insert (x : nat) (l : list nat) :=
   match l with
      | nil => x :: nil
      | hd :: tl => if (x <=? hd)%nat then x :: hd :: tl else hd :: insert x tl
   end.

Fixpoint insertion_sort (l : list nat) :=
   match l with
      | nil => nil
      | hd :: tl => insert hd (insertion_sort tl)     
   end.


Axiom gt_le_dec : forall x y : nat, {x > y} + {x <= y}.
Axiom ge_lt_dec : forall x y : nat, {x >= y} + {x < y}.

Lemma insert_keeps_list_sorted (x : nat) (l : list nat):
   order l -> order (insert x l).
Proof.
   intros.
   induction l.
   - auto.
   - simpl.
     case_eq (x <=? a).
     + intro.
       simpl.
       firstorder.
       now apply Nat.leb_le 
     + intro.
       Admitted.
       
Lemma sorted_list :
   forall l : list nat, order (insertion_sort l).
Proof.
   intro.
   induction l.
   - now simpl.
   - simpl.
     now apply insert_keeps_list_sorted. 
Qed.

Fixpoint num_occ (x : nat) (l : list nat) : nat :=
  match l with
    | nil => O
    | y :: l' =>
      if x =? y then S (num_occ x l') else num_occ x l'
  end.

Lemma occurrence_of_x (x : nat) (l : list nat) :
    num_occ x (insert x l) = S (num_occ x l).
Proof.   
   induction l.
   - simpl.
     now rewrite Nat.eqb_refl.
   - simpl.
     case_eq (x <=? a)%nat.
     + intro.
       case_eq (x =? a)%nat.
       * intro.
         replace a with x.
         simpl.
         replace (x =? x)%nat with true.
         auto.
         now rewrite Nat.eqb_refl.
         auto.
         now apply Nat.eqb_eq.
       * intro.
         simpl.
         replace (x =? a)%nat with false.
         replace (x =? x)%nat with true.
         auto.
         now rewrite Nat.eqb_refl.
     + intro.
       case_eq (x =? a)%nat.
       * intro.
         replace a with x.
         simpl.
         replace (x =? x)%nat with true.
         auto.
         now rewrite Nat.eqb_refl.
         now apply Nat.eqb_eq.
       * intro.
         simpl.
         now replace (x =? a)%nat with false.
Qed.


Lemma occurrence_of_xx(x y : nat) (l : list nat) :
    ((x =? y)%nat = false) -> num_occ x (insert y l) = num_occ x l.
Proof.
   intro.
   induction l.
   - simpl.
     now replace (x =? y)%nat with false.
   - simpl.
     case_eq (y <=? a)%nat.
     + intro.
       case_eq (x =? a)%nat.
       * intro.
         replace a with x.
         simpl.
         replace (x =? y)%nat with false.
         replace (x =? x)%nat with true.
         auto.
         now rewrite Nat.eqb_refl.
         now apply Nat.eqb_eq.
       * intro.
         simpl.
         replace (x =? y)%nat with false.
         now replace (x =? a)%nat with false.
     + intro.
       case_eq (x =? a)%nat.
       * intro.
         simpl.
         replace (x =? a)%nat with true.
         auto.
       * intro.
         simpl.
         now replace (x =? a)%nat with false.
Qed.

Definition permut (l1 l2 : list nat) :=
  forall x : nat, num_occ x l1 = num_occ x l2.

Lemma permuted_list :
   forall l : list nat, permut l (insertion_sort l).
Proof.
   intro.
   induction l.
   - firstorder.
   - intro.
     simpl.
     case_eq (x =? a)%nat.
     + intro.
       replace a with x.
       * rewrite (occurrence_of_x x (insertion_sort l)).
         now rewrite IHl.         
       * now apply Nat.eqb_eq.
     + intro.
       rewrite (occurrence_of_xx x a).
       * now rewrite IHl.         
       * assumption.  
Qed.

Theorem insertion_sorts :
   forall l : list nat, permut l (insertion_sort l) /\ order (insertion_sort l).
Proof.   
   split.
   apply permuted_list.
   apply sorted_list.
Qed.
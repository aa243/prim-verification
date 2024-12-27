Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.FixedPoint.
Require Import PL.Monad.
Import SetsNotation
       KleeneFix Sets_CPO
       Monad
       MonadNotation.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

Module SetMonadExamples4.
Import SetMonadHoare
       SetMonadOperator0
       SetMonadOperator1
       ListNotations.

(** * 程序验证案例一：归并排序中的归并步骤 *)

Definition body_merge:
  list Z * list Z * list Z ->
  SetMonad.M (ContinueOrBreak (list Z * list Z * list Z) (list Z)) :=
  fun '(l1, l2, l3) =>
    match l1, l2 with 
    | nil, _ => break (l3 ++ l2)
    | _, nil => break (l3 ++ l1)
    | x :: l1', y :: l2' =>
        choice
          (test (x <= y);; continue (l1', l2, l3 ++ x :: nil))
          (test (y <= x);; continue (l1, l2', l3 ++ y :: nil))
  end.

Definition merge l l0 :=
  repeat_break body_merge (l, l0, nil).

Fixpoint incr_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ incr_aux l0 y
  end.

Definition incr (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => incr_aux l0 x
  end.

Theorem merge_perm:
  forall l1 l2,
    Hoare (merge l1 l2) (Permutation (l1 ++ l2)).
Proof.
  intros.
  unfold merge.
  apply (Hoare_repeat_break _
           (fun '(l1', l2', l3') =>
              Permutation (l1 ++ l2) (l1' ++ l2' ++ l3'))).
  2: {
    rewrite app_nil_r.
    reflexivity.
  }
  intros [[l1' l2'] l3'] ?.
  unfold body_merge.
  destruct l1' as [ | x l1']; [| destruct l2' as [| y l2']].
  + apply Hoare_ret.
    rewrite H; simpl.
    apply Permutation_app_comm.
  + apply Hoare_ret.
    rewrite H.
    rewrite Permutation_app_comm.
    reflexivity.
  + apply Hoare_choice; apply Hoare_test_bind; intros.
    - apply Hoare_ret.
      rewrite H.
      rewrite ! app_assoc.
      simpl.
      rewrite (Permutation_app_comm _ [x]).
      reflexivity.
    - apply Hoare_ret.
      rewrite H.
      apply Permutation_app; [reflexivity |].
      rewrite ! app_assoc.
      rewrite (Permutation_app_comm _ [y]).
      reflexivity.
Qed.

Lemma incr_app_cons: forall l1 x l2,
  incr (l1 ++ [x]) ->
  incr (x :: l2) ->
  incr (l1 ++ x :: l2).
Proof.
  intros.
  simpl in H0.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv1: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (l1 ++ [x]).
Proof.
  intros.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv2: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (x :: l2).
Proof.
  intros.
  simpl.
  induction l1; simpl in *.
  + tauto.
  + apply IHl1.
    destruct l1; simpl in *; tauto.
Qed.

Theorem merge_incr:
  forall l1 l2,
    incr l1 ->
    incr l2 ->
    Hoare (merge l1 l2) (fun l3 => incr l3).
Proof.
  intros.
  unfold merge.
  apply (Hoare_repeat_break _
           (fun '(l1', l2', l3') => 
              incr (l3' ++ l1') /\
              incr (l3' ++ l2'))).
  2: {
    tauto.
  }
  clear l1 l2 H H0.
  intros [[l1 l2] l3] [? ?].
  destruct l1 as [ | x l1]; [| destruct l2 as [| y l2]].
  + apply Hoare_ret; tauto.
  + apply Hoare_ret; tauto.
  + apply Hoare_choice; apply Hoare_test_bind; intros.
    - apply Hoare_ret.
      split.
      * rewrite <- app_assoc.
        exact H.
      * rewrite <- app_assoc.
        simpl.
        apply incr_app_cons_inv1 in H.
        apply incr_app_cons_inv2 in H0.
        apply incr_app_cons; simpl in *; tauto.
    - apply Hoare_ret.
      split.
      * rewrite <- app_assoc.
        simpl.
        apply incr_app_cons_inv1 in H0.
        apply incr_app_cons_inv2 in H.
        apply incr_app_cons; simpl in *; tauto.
      * rewrite <- app_assoc.
        exact H0.
Qed.

Theorem functional_correctness_merge:
  forall l1 l2,
    incr l1 ->
    incr l2 ->
    Hoare (merge l1 l2)
          (fun l3 => Permutation (l1 ++ l2) l3 /\ incr l3).
Proof.
  intros.
  apply Hoare_conjunct.
  + apply merge_perm.
  + apply merge_incr; tauto.
Qed.

(** * 程序验证案例二：归并排序 *)

(** 一个任意的外部排序算法 *)
Definition ext_sort (l: list Z): SetMonad.M (list Z) :=
  fun l' => Permutation l l' /\ incr l'.

Definition ext_split (l: list Z): SetMonad.M (list Z * list Z) :=
  fun '(l0, l1) => Permutation l (l0 ++ l1).

Definition gmergesort_f (W: list Z -> SetMonad.M (list Z)):
  list Z -> SetMonad.M (list Z) :=
  fun x => 
    choice
      (ext_sort x)
      (test (length x >= 2)%nat;;
       '(p1, q1) <- ext_split x ;; 
       p2 <- W (p1) ;; 
       q2 <- W (q1) ;; 
       merge p2 q2).

Definition gmergesort := Kleene_LFix gmergesort_f.

Lemma ext_sort_fact:
  forall l,
    Hoare (ext_sort l) (fun l0 => Permutation l l0 /\ incr l0).
Proof.
  unfold Hoare, ext_sort; sets_unfold.
  intros.
  tauto.
Qed.

Lemma ext_split_fact:
  forall l,
    Hoare (ext_split l) (fun '(l1, l2) => Permutation l (l1 ++ l2)).
Proof.
  unfold Hoare, ext_split; sets_unfold.
  intros.
  tauto.
Qed.

Theorem functional_correctness_mergesort:
  forall l,
    Hoare (gmergesort l) (fun l0 => Permutation l l0 /\ incr l0).
Proof.
  intros.
  unfold Hoare, gmergesort, Kleene_LFix; unfold_CPO_defs.
  intros.
  destruct H as [n ?].
  revert l a H.
  change (forall l,
          Hoare (Nat.iter n gmergesort_f ∅ l)
                (fun l0 => Permutation l l0 /\ incr l0)).
  induction n; simpl; intros.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold gmergesort_f at 1.
    apply Hoare_choice; [apply ext_sort_fact |].
    apply Hoare_test_bind.
    intros.
    eapply Hoare_bind; [apply ext_split_fact |].
    intros [l1 l2] ?.
    eapply Hoare_bind; [apply IHn |].
    intros l1' [? ?].
    eapply Hoare_bind; [apply IHn |].
    intros l2' [? ?].
    eapply Hoare_conseq; [| apply functional_correctness_merge; tauto].
    intros l3 [? ?].
    rewrite <- H5 at 1.
    rewrite <- H1, <- H3.
    tauto.
Qed.

End SetMonadExamples4.

Module SetMonadOperator2.
Import SetMonadHoare
       SetMonadOperator0
       SetMonadOperator1
       SetMonadProperties0
       SetMonadHoare.

Arguments bind: simpl never.
Arguments ret: simpl never.

Fixpoint list_iter
           {A B: Type}
           (f: A -> B -> SetMonad.M B)
           (l: list A)
           (b: B):
  SetMonad.M B :=
  match l with
  | nil => ret b
  | a :: l0 => b0 <- f a b;; list_iter f l0 b0
  end.

Check rev_ind.

Theorem Hoare_list_iter {A B: Type}:
  forall (f: A -> B -> SetMonad.M B)
         (P: list A -> B -> Prop),
    (forall b l a,
       P l b ->
       Hoare (f a b) (fun b0 => P (l ++ a :: nil) b0)) ->
    forall b l, P nil b -> Hoare (list_iter f l b) (fun b0 => P l b0).
Proof.
  (** 此处的证明需要对list使用反向归纳法。*)
  intros.
  pattern l.
  refine (rev_ind _ _ _ l); simpl.
  + apply Hoare_ret.
    apply H0.
  + intros.
    (** 此时需要将_[list_iter f (l0 ++ [x]) b]_变换为
        _[b0 <- list_iter f l0 b;; f x b]_。
        我们先来证明这一条引理。*)
Abort.

(************)
(** 习题：  *)
(************)

Lemma list_iter_app:
  forall {A B: Type}
         (f: A -> B -> SetMonad.M B)
         (l1 l2: list A)
         (b: B),
    b0 <- list_iter f l1 b;; list_iter f l2 b0 ==
    list_iter f (l1 ++ l2) b.
Proof.
  intros.
  revert b.
  induction l1; simpl; intros.
  + rewrite bind_ret_l.
    reflexivity.
  + rewrite bind_assoc.
    apply bind_congr.
    - reflexivity.
    - intros b0.
      apply IHl1.
Qed.

(************)
(** 习题：  *)
(************)

#[export] Instance Hoare_congr {A: Type}:
  Proper (Sets.equiv ==> eq ==> iff) (@Hoare A).
Proof.
  unfold Proper, respectful, Hoare.
  intros.
  subst y0.
  split; intros.
  + rewrite <- H in H1.
    apply H0.
    apply H1.
  + rewrite H in H1.
    apply H0.
    apply H1.
Qed.

(************)
(** 习题：  *)
(************)

Theorem Hoare_list_iter {A B: Type}:
  forall (f: A -> B -> SetMonad.M B)
         (P: list A -> B -> Prop),
    (forall b l a,
       P l b ->
       Hoare (f a b) (fun b0 => P (l ++ a :: nil) b0)) ->
    (forall b l, P nil b -> Hoare (list_iter f l b) (fun b0 => P l b0)).
Proof.
  intros.
  pattern l.
  refine (rev_ind _ _ _ l); simpl.
  + apply Hoare_ret.
    apply H0.
  + intros.
    rewrite <- list_iter_app.
    eapply Hoare_bind.
    1 : { apply H1. }
    intros b0 ?.
    simpl in H2.
    simpl.
    rewrite bind_ret_r.
    apply H.
    apply H2.
Qed.


Import SetMonadExamples4.


Definition insertion (x: Z) (l: list Z): SetMonad.M (list Z) :=
  fun l' => exists l1 l2,
    l = l1 ++ l2 /\ l' = l1 ++ x :: l2 /\ incr l'.

Definition ins_sort (l: list Z) :=
  list_iter insertion l nil.

(************)
(** 习题：  *)
(************)

Theorem ins_sort_perm:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => Permutation L l).
Proof.
  intros.
  unfold ins_sort.
  apply (Hoare_list_iter _ (fun L l => Permutation L l)).
  + intros.
    unfold Hoare, insertion.
    sets_unfold.
    intros.
    destruct H0 as [l1 [l2 ?]].
    destruct H0.
    destruct H1.
    rewrite H1.
    rewrite H.
    rewrite H0.
    rewrite Permutation_app_comm.
    simpl.
    change (a :: l1 ++ l2) with ((a :: nil) ++ l1 ++ l2).
    change (l1 ++ a :: l2) with (l1 ++ a :: nil ++ l2).
    change ((a :: nil) ++ l1 ++ l2) with (((a :: nil) ++ l1) ++ l2).
    change (l1 ++ a :: nil ++ l2) with (l1 ++ (a :: nil) ++ l2).
    rewrite app_assoc.
    apply Permutation_app.
    * apply Permutation_app_comm.
    * reflexivity.
  + reflexivity.
Qed. 



(************)
(** 习题：  *)
(************)

Theorem ins_sort_incr:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => incr l).
Proof.
  intros.
  unfold ins_sort.
  apply (Hoare_list_iter _ (fun L l => incr l)).
  + intros l _ a H.
    unfold Hoare, insertion.
    sets_unfold.
    intros.
    destruct H0 as [l1 [l2 ?]].
    tauto.
  + simpl.
    tauto.
Qed. 

Theorem functional_correctness_ins_sort:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => Permutation L l /\ incr l).
Proof.
  intros.
  apply Hoare_conjunct.
  + apply ins_sort_perm.
  + apply ins_sort_incr.
Qed.

End SetMonadOperator2.

(**
DFS :
When at vertex u, 






*)

Module StateRelMonad.

Definition M (Σ A: Type) : Type :=
  Σ -> A -> Σ -> Prop.
(** (s1, a, s2) ∈ p *)

Definition ret (Σ A: Type) (a0: A) : M Σ A :=
  fun s1 a s2 => a = a0 /\ s1 = s2.

Definition bind (Σ A B: Type) (f : M Σ A) (g : A -> M Σ B) : M Σ B :=
  fun s1 b s3 => exists s2 a, f s1 a s2 /\ g a s2 b s3.

End StateRelMonad.

Import SetMonadOperator1.

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
  { ret := StateRelMonad.ret Σ;
    bind := StateRelMonad.bind Σ }.

Definition choice {Σ A: Type} (f g: StateRelMonad.M Σ A): StateRelMonad.M Σ A :=
  f ∪ g.

Definition any {Σ: Type} (A: Type): StateRelMonad.M Σ A :=
  fun s1 a s2 => s1 = s2.

Definition test {Σ: Type} (P: Σ -> Prop): StateRelMonad.M Σ unit :=
  fun s1 _ s2 => P s1 /\ s1 = s2.

Definition repeat_break_f
            {Σ A B: Type}
            (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B))
            (W: A -> StateRelMonad.M Σ B)
            (a: A): StateRelMonad.M Σ B :=
            x <- body a;;
            match x with
            | by_continue a' => W a'
            | by_break b => ret b
end.

Definition repeat_break
  {Σ A B: Type}
  (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B)):
A -> StateRelMonad.M Σ B :=
Kleene_LFix (repeat_break_f body).

Definition continue {Σ A B: Type} (a: A):
  StateRelMonad.M Σ (ContinueOrBreak A B) :=
  ret (by_continue a).

Definition break {Σ A B: Type} (b: B):
  StateRelMonad.M Σ (ContinueOrBreak A B) :=
  ret (by_break b).


Record PreGraph (Vertex Edge: Type) : Type :=
  { vvalid: Vertex -> Prop;
    evalid: Edge -> Prop;
    src: Edge -> Vertex;
    dst: Edge -> Vertex 
  }.

Notation "pg '.(vvalid)'" := (vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).

Record step_aux {V E: Type} (pg: PreGraph V E) (e : E) (x y: V) : Prop :=
  { step_evalid: e ∈ pg.(evalid);
    step_src_vvalid: x ∈ pg.(vvalid);
    step_dst_vvalid: y ∈ pg.(vvalid);
    step_src: x = pg.(src) e;
    step_dst: y = pg.(dst) e
  }.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V) : Prop :=
  exists e: E, step_aux pg e x y.

Definition reachable {V E: Type} (pg: PreGraph V E): V -> V -> Prop :=
  clos_refl_trans (step pg).

Record state (V: Type): Type :=
{ visited: V -> Prop;
  stack: list V;
}.

Notation "s '.(visited)'" := (visited _ s) (at level 1).
Notation "s '.(stack)'" := (stack _ s) (at level 1).


Definition test_unvisited {V: Type} (v: V): StateRelMonad.M (state V) unit :=
  test (fun s => ~ s.(visited) v).

Definition test_all_neighbour_visited {V E: Type} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) unit :=
  test (fun s => forall v, step pg u v -> v ∈ s.(visited)).

Definition visit {V: Type} (v: V): StateRelMonad.M (state V) unit :=
  fun s1 _ s2 =>
    s2.(visited) == s1.(visited) ∪ Sets.singleton v /\
    s2.(stack) = v :: s1.(stack).

Definition push_stack {V: Type} (v: V): StateRelMonad.M (state V) unit :=
  fun s1 _ s2 => s2.(stack) = v :: s1.(stack) /\ s2.(visited) == s1.(visited).

Definition pop_stack {V: Type}: StateRelMonad.M (state V) V :=
  fun s1 v s2 => s2.(visited) == s1.(visited) /\ 
                s1.(stack) = v :: s2.(stack).

Definition test_empty_stack {V: Type}: StateRelMonad.M (state V) unit :=
  test (fun s => s.(stack) = nil).

Definition body_DFS {V E: Type} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) (ContinueOrBreak V unit) :=
  choice
    (v <- any V;;
     test_unvisited v;;
     test (fun _ => step pg u v);;
     push_stack u;;
     visit v;;
     continue v)
    (test_all_neighbour_visited pg u;;
    choice
      (v <- pop_stack;;
       continue v)
       (test_empty_stack;;
        break tt)).

Definition DFS {V E: Type} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) unit :=
  repeat_break (body_DFS pg) u.

Definition Hoare {Σ A: Type} (P: Σ -> Prop) (c: StateRelMonad.M Σ A) (Q: A -> Σ -> Prop): Prop :=
  forall σ1 a σ2, P σ1 -> c σ1 a σ2 -> Q a σ2.

Theorem functional_correctness_DFS {V E: Type} (pg: PreGraph V E):
  forall u: V,
    Hoare (fun s => s.(visited) == Sets.singleton u /\ s.(stack) = nil)
          (DFS pg u)
          (fun _ s => s.(visited) == (reachable pg u)).
Abort.

Theorem  Hoare_bind {Σ A B: Type}:
  forall (P: Σ -> Prop) (f: StateRelMonad.M Σ A) (M: A -> Σ -> Prop)
  (g: A -> StateRelMonad.M Σ B) (Q: B -> Σ -> Prop),
  Hoare P f M ->
  (forall a: A, Hoare (M a) (g a) Q) ->
  Hoare P (bind f g) Q.
Proof.
  intros.
  unfold Hoare, bind; sets_unfold; simpl; unfold StateRelMonad.bind.
  intros σ1 b σ3 ? ?.
  destruct H2 as [a [σ2 [? ?]]].
  pose proof H _ _ _ H1 H2.
  pose proof H0 σ2 _ _ _ H4 H3.
  apply H5.
Qed.

Theorem Hoare_ret {Σ A: Type}:
  forall (a0: A) (P: A -> Σ -> Prop),
    Hoare (P a0) (ret a0) P.
Proof.
  intros.
  unfold Hoare, ret; sets_unfold; simpl; unfold StateRelMonad.ret.
  intros.
  destruct H0; subst; tauto.
Qed.

Theorem Hoare_choice {Σ A: Type}:
  forall (P: Σ -> Prop) (f g: StateRelMonad.M Σ A) (Q: A -> Σ -> Prop),
    Hoare P f Q ->
    Hoare P g Q ->
    Hoare P (choice f g) Q.
Proof.
  intros.
  unfold Hoare, choice; sets_unfold; simpl.
  intros.
  destruct H2.
  + apply (H _ _ _ H1 H2).
  + apply (H0 _ _ _ H1 H2).
Qed.

Theorem Hoare_test_bind {Σ A: Type}:
  forall (P Q: Σ -> Prop) (f: StateRelMonad.M Σ A) R,
    Hoare (fun s => Q s /\ P s) f R ->
    Hoare P (test Q;; f) R.
Proof.
  intros.
  eapply Hoare_bind; [| intros x; apply H].
  unfold Hoare, test; sets_unfold; simpl.
  intros.
  destruct H1.
  subst σ2.
  tauto.
Qed.

Theorem Hoare_any {Σ: Type}: 
  forall (A: Type) (P: Σ -> Prop),
    Hoare P (any A) (fun _ => P).
Proof.
  intros.
  unfold Hoare, any; sets_unfold; simpl.
  intros.
  subst σ2.
  tauto.
Qed.

Theorem Hoare_conseq {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q1 Q2: A -> Σ -> Prop),
    (forall σ, P1 σ -> P2 σ) ->
    (forall a σ, Q2 a σ -> Q1 a σ) ->
    Hoare P2 f Q2 ->
    Hoare P1 f Q1.
Proof.
  intros.
  unfold Hoare; intros.
  apply H0.
  apply (H1 σ1 a σ2).
  + apply H; tauto.
  + tauto.
Qed.

Theorem Hoare_conseq_pre {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q: A -> Σ -> Prop),
    (forall σ, P1 σ -> P2 σ) ->
    Hoare P2 f Q ->
    Hoare P1 f Q.
Proof.
  intros.
  eapply Hoare_conseq; eauto.
Qed.

Theorem Hoare_conseq_post {Σ A: Type}:
  forall (P: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q1 Q2: A -> Σ -> Prop),
    (forall a σ, Q2 a σ -> Q1 a σ) ->
    Hoare P f Q2 ->
    Hoare P f Q1.
Proof.
  intros.
  eapply Hoare_conseq; eauto.
Qed.

Theorem Hoare_conjunct {Σ A: Type}:
  forall (P: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q1 Q2: A -> Σ -> Prop),
    Hoare P f Q1 ->
    Hoare P f Q2 ->
    Hoare P f (fun a σ => Q1 a σ /\ Q2 a σ).
Proof.
  intros.
  unfold Hoare; intros.
  split.
  + apply (H σ1 a σ2); tauto.
  + apply (H0 σ1 a σ2); tauto.
Qed.

Theorem Hoare_forall {Σ A: Type}:
  forall (X: Type) (P: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q: X -> A -> Σ -> Prop),
    (forall x, Hoare P f (Q x)) ->
    Hoare P f (fun a s => forall x, Q x a s).
Proof.
  intros.
  unfold Hoare; intros.
  apply (H x _ _ _ H0 H1).
Qed.

Theorem Hoare_pre_ex {Σ A: Type}:
  forall (X: Type) (P: X -> Σ -> Prop) (f: StateRelMonad.M Σ A) (Q: A -> Σ -> Prop),
    (forall x, Hoare (P x) f Q) ->
    Hoare (fun s => exists x, P x s) f Q.
Proof.
  intros.
  unfold Hoare; intros.
  destruct H0 as [x ?].
  apply (H x _ _ _ H0 H1).
Qed.

Theorem Hoare_repeat_break {A B Σ: Type}:
  forall (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B))
         (P: A -> Σ -> Prop)
         (Q: B -> Σ -> Prop),
    (forall a, Hoare (P a) (body a) (fun x s => match x with
                                        | by_continue a => P a s
                                        | by_break b => Q b s
                                        end)) ->
    (forall a, Hoare (P a) (repeat_break body a) Q).
Proof.
  intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold repeat_break, Kleene_LFix; unfold_CPO_defs.
  intros [n ?].
  revert a s1 b s2 H0 H1.
  change (forall a, Hoare (P a) (Nat.iter n (repeat_break_f body) ∅ a) Q).
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold repeat_break_f at 1.
    eapply Hoare_bind.
    - apply H.
    - intros [a0 | b0].
      * apply IHn.
      * apply Hoare_ret.
Qed.

Definition I1 {V E: Type} (pg: PreGraph V E) (u: V): V -> Prop :=
  fun v => reachable pg u v.

Definition I2 {V E: Type} (pg: PreGraph V E) (u: V): state V -> Prop :=
  fun s => forall v : V, In v s.(stack) -> reachable pg u v.


Definition reachable_via_sets {V E: Type} (pg: PreGraph V E) (P: V -> Prop): V -> V -> Prop :=
  clos_refl_trans (fun x y => step pg x y /\ P y).

Definition I4 {V E: Type} (pg: PreGraph V E) : V -> state V -> V -> Prop :=
  fun v s u1 => u1 ∈ s.(visited) -> exists u0, reachable_via_sets pg (s.(visited)) u0 u1.

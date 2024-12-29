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
    Hoare (merge l1 l2) incr.
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

Theorem Hoare_list_iter {A B: Type}:
  forall (f: A -> B -> SetMonad.M B)
         (P: list A -> B -> Prop),
    (forall b l a,
       P l b ->
       Hoare (f a b) (fun b0 => P (l ++ a :: nil) b0)) ->
    (forall b l, P nil b -> Hoare (list_iter f l b) (fun b0 => P l b0)).
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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

#[export] Instance Hoare_congr {A: Type}:
  Proper (Sets.equiv ==> eq ==> iff) (@Hoare A).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Theorem ins_sort_incr:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => incr l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

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

(** * 表示带程序状态计算的单子 *)


(** 下面用StateRelMonad表示带有程序状态的非确定性计算。*)

Module StateRelMonad.

Definition M (Σ A: Type): Type :=
  Σ -> A -> Σ -> Prop.

Definition bind (Σ A B: Type) (f: M Σ A) (g: A -> M Σ B): M Σ B :=
  fun (s1: Σ) (b: B) (s3: Σ) =>
    exists (a: A) (s2: Σ),
      (s1, a, s2) ∈ f /\ (s2, b, s3) ∈ g a.

Definition ret (Σ A: Type) (a0: A): M Σ A :=
  fun (s1: Σ) (a: A) (s2: Σ) => a = a0 /\ s1 = s2.

End StateRelMonad.

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
{|
  bind := StateRelMonad.bind Σ;
  ret := StateRelMonad.ret Σ;
|}.

Module StateRelMonadOp.
Import SetMonadOperator1.


(** 下面用StateRelMonad表示带有程序状态的非确定性计算。*)

Module StateRelMonad.

Definition M (Σ A: Type): Type :=
  Σ -> A -> Σ -> Prop.

Definition bind (Σ A B: Type) (f: M Σ A) (g: A -> M Σ B): M Σ B :=
  fun (s1: Σ) (b: B) (s3: Σ) =>
    exists (a: A) (s2: Σ),
      (s1, a, s2) ∈ f /\ (s2, b, s3) ∈ g a.

Definition ret (Σ A: Type) (a0: A): M Σ A :=
  fun (s1: Σ) (a: A) (s2: Σ) => a = a0 /\ s1 = s2.

End StateRelMonad.

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
{|
  bind := StateRelMonad.bind Σ;
  ret := StateRelMonad.ret Σ;
|}.

(** 以下可以再定义一些额外的算子。*)

Definition test {Σ: Type} (P: Σ -> Prop): StateRelMonad.M Σ unit :=
  fun s1 _ s2 => P s1 /\ s1 = s2.

Definition choice {Σ A: Type} (f g: StateRelMonad.M Σ A): StateRelMonad.M Σ A :=
  f ∪ g.

Definition any {Σ: Type} (A: Type): StateRelMonad.M Σ A :=
  fun s1 _ s2 => s1 = s2.

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

End StateRelMonadOp.

(** 可以如下定义有向图。*)

Record PreGraph (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

Notation "pg '.(vvalid)'" := (vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).

(** 基于此就能定义“从x点经过一条边可以到达y点”。*)

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y.

(** 进一步，单步可达关系的自反传递闭包就是多步可达关系。*)

Definition reachable {V E: Type} (pg: PreGraph V E) :=
  clos_refl_trans (step pg).


(** 自反传递闭包_[clos_refl_trans]_是SetsClass库提供的定义。*)


Module StateRelMonadExample.
Import SetMonadOperator1
       StateRelMonadOp.

(** 下面定义DFS算法的程序状态，每个程序状态包含一个_[visitied]_集合与一个栈。*)

Record state (V: Type): Type :=
{
  stack: list V;
  visited: V -> Prop;
}.

Definition unvisited (V: Type) (s: state V): V -> Prop :=
  Sets.complement (visited V s).

Notation "s '.(visited)'" := (visited _ s) (at level 1).
Notation "s '.(unvisited)'" := (unvisited _ s) (at level 1).
Notation "s '.(stack)'" := (stack _ s) (at level 1).

Lemma unvisited_visited {V: Type}:
  forall (s: state V),
    s.(unvisited) == Sets.complement s.(visited).
Proof. intros. reflexivity. Qed.

(** 基于此就可以定义DFS中需要用到的程序状态基本操作。*)

Definition test_unvisited {V} (v: V): StateRelMonad.M (state V) unit :=
  test (fun s => ~ v ∈ s.(visited)).

Definition test_all_neighbor_visited {V E} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) unit :=
    test (fun s => forall v, step pg u v -> v ∈ s.(visited)).

Definition visit {V} (v: V): StateRelMonad.M (state V) unit :=
  fun s1 _ s2 =>
    s2.(visited) == s1.(visited) ∪ Sets.singleton v /\
    s2.(stack) = s1.(stack).

Definition push_stack {V} (v: V): StateRelMonad.M (state V) unit :=
  fun s1 _ s2 =>
    s2.(stack) = v :: s1.(stack) /\ s2.(visited) = s1.(visited).

Definition pop_stack {V}: StateRelMonad.M (state V) V :=
  fun s1 v s2 =>
    s1.(stack) = v :: s2.(stack) /\ s2.(visited) = s1.(visited).

Definition test_empty_stack {V}: StateRelMonad.M (state V) unit :=
  test (fun s => s.(stack) = nil).

(** 以下是DFS算法的描述。*)

Definition body_DFS {V E} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) (ContinueOrBreak V unit) :=
  choice
    (v <- any V;;
     test_unvisited v;;
     test (fun _ => step pg u v);;
     push_stack u;;
     visit v;;
     continue v)
    (test_all_neighbor_visited pg u;;
      choice
      (v <- pop_stack;;
       continue v)
      (test_empty_stack;;
       break tt)).

Definition DFS {V E} (pg: PreGraph V E) (u: V):
  StateRelMonad.M (state V) unit :=
  repeat_break (body_DFS pg) u.

End StateRelMonadExample.

Module StateRelMonadHoare.
Import SetMonadOperator1
       StateRelMonadOp.


(** 在StateRelMonad上的霍尔逻辑是一个关于霍尔三元组的逻辑。*)

Definition Hoare {Σ A: Type}
                 (P: Σ -> Prop)
                 (c: StateRelMonad.M Σ A)
                 (Q: A -> Σ -> Prop): Prop :=
  forall s1 a s2, P s1 -> (s1, a, s2) ∈ c -> Q a s2.

Theorem Hoare_bind {Σ A B: Type}:
  forall (P: Σ -> Prop)
         (f: StateRelMonad.M Σ A)
         (Q: A -> Σ -> Prop)
         (g: A -> StateRelMonad.M Σ B)
         (R: B -> Σ -> Prop),
  Hoare P f Q ->
  (forall a, Hoare (Q a) (g a) R) ->
  Hoare P (bind f g) R.
Proof.
  intros.
  unfold Hoare, bind; simpl; sets_unfold; unfold StateRelMonad.bind.
  intros s1 b s3 ? [a [s2 [? ?]]].
  pose proof H _ _ _ H1 H2.
  pose proof H0 a _ _ _ H4 H3.
  tauto.
Qed.

Theorem Hoare_ret {Σ A: Type}:
  forall (P: A -> Σ -> Prop) (a0: A),
    Hoare (P a0) (ret a0) P.
Proof.
  intros.
  unfold Hoare, ret; simpl; sets_unfold; unfold StateRelMonad.ret.
  intros.
  destruct H0; subst; tauto.
Qed.

Theorem Hoare_choice {Σ A: Type}:
  forall P (f g: StateRelMonad.M Σ A) Q,
    Hoare P f Q -> 
    Hoare P g Q ->
    Hoare P (choice f g) Q.
Proof.
  intros.
  unfold Hoare, choice; sets_unfold.
  intros ? ? ? ? [? | ?].
  + pose proof H _ _ _ H1 H2.
    tauto.
  + pose proof H0 _ _ _ H1 H2.
    tauto.
Qed.

Theorem Hoare_test_bind {Σ A: Type}:
  forall P (Q: Σ -> Prop) (f: StateRelMonad.M Σ A) R,
    Hoare (fun s => Q s /\ P s) f R -> 
    Hoare P (test Q;; f) R.
Proof.
  intros.
  eapply Hoare_bind; [| intros; apply H].
  unfold Hoare, test; sets_unfold.
  intros s1 _ s2 ? [? ?].
  subst; tauto.
Qed.

Theorem Hoare_any {Σ A: Type}:
  forall (P: Σ -> Prop),
    Hoare P (any A) (fun _ => P).
Proof.
  unfold Hoare, any; sets_unfold.
  intros.
  subst; tauto.
Qed.

Theorem Hoare_conseq {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    (forall s, P1 s -> P2 s) ->
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare P2 f Q2 ->
    Hoare P1 f Q1.
Proof.
  intros.
  unfold Hoare.
  intros.
  apply H0.
  apply (H1 s1 a s2).
  + apply H; tauto.
  + tauto.
Qed.

Theorem Hoare_conseq_pre {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall s, P1 s -> P2 s) ->
    Hoare P2 f Q ->
    Hoare P1 f Q.
Proof.
  intros.
  unfold Hoare.
  intros.
  apply (H0 s1 a s2).
  + apply H; tauto.
  + tauto.
Qed.

Theorem Hoare_conseq_post {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare P f Q2 ->
    Hoare P f Q1.
Proof.
  intros.
  unfold Hoare.
  intros.
  apply H.
  apply (H0 s1 a s2); tauto.
Qed.

Theorem Hoare_conj {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    Hoare P f Q1 ->
    Hoare P f Q2 ->
    Hoare P f (fun a s => Q1 a s /\ Q2 a s).
Proof.
  intros.
  unfold Hoare; intros.
  split.
  + apply (H _ _ _ H1 H2).
  + apply (H0 _ _ _ H1 H2).
Qed.  

Theorem Hoare_forall {Σ A: Type}:
  forall (X: Type) (P: Σ -> Prop) f (Q: X -> A -> Σ -> Prop),
    (forall x, Hoare P f (Q x)) ->
    Hoare P f (fun a s => forall x, Q x a s).
Proof.
  intros.
  unfold Hoare.
  intros.
  apply (H x _ _ _ H0 H1).
Qed.

Theorem Hoare_pre_ex {Σ A: Type}:
  forall (X: Type) (P: X -> Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall x, Hoare (P x) f Q) ->
    Hoare (fun s => exists x, P x s) f Q.
Proof.
  intros.
  unfold Hoare.
  intros s1 a s2 [x ?] ?.
  apply (H x _ _ _ H0 H1).
Qed.

Theorem Hoare_ret' {Σ A: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (a0: A),
    (forall s, P s -> Q a0 s) ->
    Hoare P (ret a0) Q.
Proof.
  intros.
  unfold Hoare, ret; simpl; sets_unfold; unfold StateRelMonad.ret.
  intros.
  destruct H1; subst.
  apply H. tauto.
Qed.

Theorem Hoare_repeat_break {Σ A B: Type}:
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

End StateRelMonadHoare.

Module DFSProof.
Import StateRelMonadExample
       SetMonadOperator1
       StateRelMonadOp
       StateRelMonadHoare.


Fact push_stack_fact {V: Type}: forall (v: V) P,
  Hoare P (push_stack v) (fun _ s => exists s', s.(stack) = v :: s'.(stack) /\ s.(visited) = s'.(visited) /\ P s').
Proof.
  intros.
  unfold Hoare, push_stack; sets_unfold.
  intros s1 _ s2 ? [? ?].
  exists s1; tauto.
Qed.

Fact pop_stack_fact {V: Type}: forall P,
  Hoare P (pop_stack) (fun (v: V) s => exists s', s'.(stack) = v :: s.(stack) /\ s.(visited) = s'.(visited) /\ P s').
Proof.
  intros.
  unfold Hoare, pop_stack; sets_unfold.
  intros s1 v s2 ? [? ?].
  exists s1; tauto.
Qed.

Fact visit_fact {V: Type}: forall (v: V) P,
  Hoare P (visit v) (fun _ s => exists s', s.(stack) = s'.(stack) /\ s.(visited) == s'.(visited) ∪ Sets.singleton v /\ P s').
Proof.
  intros.
  unfold Hoare, visit; sets_unfold.
  intros s1 _ s2 ? [? ?].
  exists s1; tauto.
Qed.

Definition I1 {V E} (pg: PreGraph V E) (u: V): V -> Prop :=
  fun v => reachable pg u v.

Definition I2 {V E} (pg: PreGraph V E) (u: V): state V -> Prop :=
  fun s => forall v, In v s.(stack) -> reachable pg u v.

Lemma DFS_stack_reachable {V E} (pg: PreGraph V E):
  forall (u v: V),
    Hoare (fun s => I1 pg u v /\ I2 pg u s)
          (body_DFS pg v)
          (fun res s =>
             match res with
             | by_continue w => I1 pg u w /\ I2 pg u s
             | by_break _ => True
             end).
Proof.
  intros.
  unfold body_DFS, I1, I2.
  apply Hoare_choice.
  + eapply Hoare_bind; [apply Hoare_any |].
    intros w.
    apply Hoare_test_bind.
    apply Hoare_test_bind.
    eapply Hoare_bind; [apply push_stack_fact | cbv beta; intros _].
    apply Hoare_pre_ex; intros s'.
    eapply Hoare_bind; [apply visit_fact | cbv beta; intros _].
    apply Hoare_pre_ex; intros s''.
    apply Hoare_ret'; intros.
    destruct H as [? [? [? [? [? [? [? ?]]]]]]].
    split.
    - transitivity_n1 v; tauto.
    - intros.
      rewrite H, H1 in H7.
      simpl in H7; destruct H7.
      * subst v0.
        tauto.
      * revert H7; apply H6.
  + apply Hoare_test_bind.
    apply Hoare_choice.
    - eapply Hoare_bind; [apply pop_stack_fact | intros w].
      apply Hoare_pre_ex; intros s'.
      apply Hoare_ret'.
      intros.
      destruct H as [? [? [? [? ?]]]].
      rewrite H in H3.
      simpl in H3.
      split.
      * apply (H3 w); tauto.
      * intros.
        apply H3; tauto.
    - apply Hoare_test_bind.
      apply Hoare_ret'.
      tauto.
Qed.

Definition I3 {V E} (pg: PreGraph V E) (u: V): state V -> Prop :=
  fun s => forall v, v ∈ s.(visited) -> reachable pg u v.


Lemma DFS_visited_reachable {V E} (pg: PreGraph V E):
  forall (u v: V),
    Hoare (fun s => I1 pg u v /\ I3 pg u s)
          (body_DFS pg v)
          (fun res s =>
             match res with
             | by_continue _ => I3 pg u s
             | by_break _ => I3 pg u s
             end).
Proof.
  intros.
  unfold body_DFS, I1, I3.
  apply Hoare_choice.
  + eapply Hoare_bind; [apply Hoare_any |].
    intros w.
    apply Hoare_test_bind.
    apply Hoare_test_bind.
    eapply Hoare_bind; [apply push_stack_fact | cbv beta; intros _].
    apply Hoare_pre_ex; intros s'.
    eapply Hoare_bind; [apply visit_fact | cbv beta; intros _].
    apply Hoare_pre_ex; intros s''.
    apply Hoare_ret'; intros.
    destruct H as [? [? [? [? [? [? [? ?]]]]]]].
    rewrite H1, H3 in H0.
    Sets_unfold1 in H0.
    destruct H0.
    - revert H0; apply H7.
    - sets_unfold in H0.
      subst v0.
      transitivity_n1 v; tauto.
  + apply Hoare_test_bind.
    apply Hoare_choice.
    - eapply Hoare_bind; [apply pop_stack_fact | intros w].
      apply Hoare_pre_ex; intros s'.
      apply Hoare_ret'.
      intros.
      destruct H as [? [? [? [? ?]]]].
      rewrite H1 in H0.
      revert H0; apply H4.
    - apply Hoare_test_bind.
      apply Hoare_ret'.
      tauto.
Qed.


End DFSProof.

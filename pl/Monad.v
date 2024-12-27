Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.FixedPoint.
Import SetsNotation.
Import KleeneFix Sets_CPO.
Local Open Scope sets.
Local Open Scope Z.

(** * 在Coq中定义单子结构 *)

(** 单子可以这样在Coq中定义为一类代数结构。*)

Module Monad.

Class Monad (M: Type -> Type): Type := {
  bind: forall {A B: Type}, M A -> (A -> M B) -> M B;
  ret: forall {A: Type}, A -> M A;
}.

End Monad.

Import Monad.

(** 我们之后最常常用到的将是集合单子（set monad）如下定义。*)

Module SetMonad.

Definition M (A: Type): Type := A -> Prop.

Definition bind: forall (A B: Type) (f: M A) (g: A -> M B), M B :=
  fun (A B: Type) (f: M A) (g: A -> M B) =>
    fun b: B => exists a: A, a ∈ f /\ b ∈ g a.

Definition ret: forall (A: Type) (a: A), M A :=
  fun (A: Type) (a: A) => Sets.singleton a.

End SetMonad.

#[export] Instance set_monad: Monad SetMonad.M := {|
  bind := SetMonad.bind;
  ret := SetMonad.ret;
|}.

(** 下面是另一个例子状态单子的定义：*)

Module StateMonad.

Definition M (Σ A: Type): Type := Σ -> Σ * A.

Definition bind (Σ: Type):
  forall (A B: Type) (f: M Σ A) (g: A -> M Σ B), M Σ B :=
  fun A B f g s1 =>
    match f s1 with
    | (s2, a) => g a s2
    end.

Definition ret (Σ: Type):
  forall (A: Type) (a: A), M Σ A :=
  fun A a s => (s, a).

End StateMonad.

#[export] Instance state_monad (Σ: Type): Monad (StateMonad.M Σ) := {|
  bind := StateMonad.bind Σ;
  ret := StateMonad.ret Σ;
|}.


Import Monad.

Module SetMonadExamples0.

(** 任取一个整数：*)

Definition any_Z: SetMonad.M Z := Sets.full.

(** 整数乘二：*)

Definition multi_two: Z -> SetMonad.M Z :=
  fun x => ret (x * 2).

(** 整数加一：*)

Definition plus_one: Z -> SetMonad.M Z :=
  fun x => ret (x + 1).

(** 任取整数再乘二：*)

Definition bind_ex0: SetMonad.M Z :=
  bind any_Z multi_two.

(** 任取整数乘二再加一：*)

Definition bind_ex1: SetMonad.M Z :=
  bind (bind any_Z multi_two) plus_one.

Definition bind_ex2: SetMonad.M Z :=
  bind any_Z (fun x => bind (multi_two x) plus_one).


End SetMonadExamples0.

(** 下面是用单子描述计算时常用的记号：*)

Module MonadNotation.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation " x : T <- c1 ;; c2" :=(bind c1 (fun x : T => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (bind c1 (fun x => match x with pat => c2 end))
  (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

Notation "e1 ;; e2" := (bind e1 (fun _: unit => e2))
  (at level 61, right associativity) : monad_scope.

End MonadNotation.
Import MonadNotation.
Local Open Scope monad.

(** 用这些Notation可以重写前面的一些例子。*)

Module SetMonadExamples1.
Import SetMonadExamples0.

(** 任取整数再乘二：*)

Definition bind_ex0': SetMonad.M Z :=
  x <- any_Z;; ret (x * 2).

(** 任取整数乘二再加一：*)

Definition bind_ex1': SetMonad.M Z :=
  x <- any_Z;; y <- multi_two x;; ret (y + 1).

End SetMonadExamples1.

(** * 集合单子的额外算子 *)

Module SetMonadOperator0.

Definition choice {A: Type} (f g: SetMonad.M A):
  SetMonad.M A :=
  f ∪ g.

Definition test (P: Prop): SetMonad.M unit :=
  fun _ => P.

End SetMonadOperator0.

Module SetMonadExamples2.
Import SetMonadOperator0.

Definition compute_abs (z: Z): SetMonad.M Z :=
  choice
    (test (z >= 0);; ret z)
    (test (z <= 0);; ret (-z)).

End SetMonadExamples2.

(** 下面证明一些集合单子算子的性质 *)

Module SetMonadProperties0.
Import SetMonadOperator0.

(** 复合算子具有单调性：*)

#[export] Instance bind_mono (A B: Type):
  Proper (Sets.included ==> Sets.included ==> Sets.included)
    (@bind _ set_monad A B).
Proof.
  unfold Proper, respectful.
  unfold set_monad, bind, SetMonad.bind;
  sets_unfold; intros f1 f2 Hf g1 g2 Hg.
  intros b [a ?]; exists a.
  specialize (Hf a); specialize (Hg a b).
  tauto.
Qed.

(** 复合算子保持集合相等：*)

#[export] Instance bind_congr (A B: Type):
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
    (@bind _ set_monad A B).
Proof.
  unfold Proper, respectful.
  unfold set_monad, bind, SetMonad.bind;
  sets_unfold; intros f1 f2 Hf g1 g2 Hg.
  intros b; split; intros [a ?]; exists a.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
Qed.

(** 复合算子具有对并集的分配律：*)

Lemma bind_union_distr_l:
  forall A B (f: SetMonad.M A) (g1 g2: A -> SetMonad.M B),
    bind f (g1 ∪ g2) == bind f g1 ∪ bind f g2.
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros b.
  split.
  + intros [a0 [? [? | ?]]].
    - left; exists a0; tauto.
    - right; exists a0; tauto.
  + intros [[a ?] | [a ?]]; exists a; tauto.
Qed.

Lemma bind_union_distr_r:
  forall A B (f1 f2: SetMonad.M A) (g: A -> SetMonad.M B),
    bind (f1 ∪ f2) g == bind f1 g ∪ bind f2 g.
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [[? | ?] ?]]; [left | right]; exists a0; tauto.
  + intros [[a0 ?] | [a0 ?]]; exists a0; tauto.
Qed.

Lemma bind_indexed_union_distr_l:
  forall A B I (f: SetMonad.M A) (g: I -> A -> SetMonad.M B),
    bind f (⋃ g) == ⋃ (fun i: I => bind f (g i)).
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [? [i ?]]]; exists i, a0; tauto.
  + intros [i [a0 ?]]; exists a0; split; [| exists i]; tauto.
Qed.

Lemma bind_indexed_union_distr_r:
  forall A B I (f: I -> SetMonad.M A) (g: A -> SetMonad.M B),
    bind (⋃ f) g == ⋃ (fun i: I => bind (f i) g).
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros.
  split.
  + intros [a0 [[i ?] ?]]; exists i, a0; tauto.
  + intros [i [a0 ?]]; exists a0; split; [exists i |]; tauto.
Qed.

(************)
(** 习题：  *)
(************)

(** 复合算子具有结合律： *)

Lemma bind_assoc:
  forall (A B C: Type)
         (f: SetMonad.M A)
         (g: A -> SetMonad.M B)
         (h: B -> SetMonad.M C),
  bind (bind f g) h ==
  bind f (fun a => bind (g a) h).
Proof.
  unfold set_monad, bind, SetMonad.bind;
  intros; sets_unfold; intros c.
  split; intros.
  + repeat destruct H.
    exists x0.
    split; [tauto |].
    exists x.
    tauto.
  + repeat destruct H.
    repeat destruct H0.
    exists x0.
    split; [ | tauto].
    exists x.
    tauto.
Qed.  

(************)
(** 习题：  *)
(************)

(** 复合算子的左单位元是ret： *)

Lemma bind_ret_l:
  forall (A B: Type)
         (a: A)
         (f: A -> SetMonad.M B),
  bind (ret a) f == f a.
Proof.
  unfold set_monad, bind, SetMonad.bind, ret, SetMonad.ret;
  intros; sets_unfold; intros b.
  split.
  + intros [a0 [? ?]].
    rewrite H.
    apply H0.
  + intros.
    exists a; tauto.
Qed.  

(************)
(** 习题：  *)
(************)

(** 复合算子的右单位元是ret： *)

Lemma bind_ret_r:
  forall (A: Type)
         (f: SetMonad.M A),
  bind f ret == f.
Proof.
  unfold set_monad, bind, SetMonad.bind, ret, SetMonad.ret;
  intros; sets_unfold; intros a.
  split.
  + intros [a0 [? ?]].
    rewrite <- H0.
    apply H.
  + intros.
    exists a; tauto.
Qed.


End SetMonadProperties0.

Module SetMonadOperator1.
Import SetMonadOperator0
       SetMonadProperties0.

(** 如果要表示带循环的计算过程，那就需要引入新的循环算子。

    首先定义循环体的计算结果，其结果要么是continue终止，要么是break终止。*)

Inductive ContinueOrBreak (A B: Type): Type :=
| by_continue (a: A)
| by_break (b: B).

Arguments by_continue {_} {_} (_).
Arguments by_break {_} {_} (_).

(** 下面用不动点定义repeat循环。*)

Definition repeat_break_f
             {A B: Type}
             (body: A -> SetMonad.M (ContinueOrBreak A B))
             (W: A -> SetMonad.M B)
             (a: A): SetMonad.M B :=
  x <- body a;;
  match x with
  | by_continue a' => W a'
  | by_break b => ret b
  end.

Definition repeat_break
             {A B: Type}
             (body: A -> SetMonad.M (ContinueOrBreak A B)):
  A -> SetMonad.M B :=
  Kleene_LFix (repeat_break_f body).

(** 下面证明_[repeat_break_f]_是单调连续的，从而表面上述不动点定理的应用是合理的。*)

Lemma repeat_break_f_mono:
  forall {A B: Type}
         (body: A -> SetMonad.M (ContinueOrBreak A B)),
  mono (repeat_break_f body).
Proof.
  intros.
  unfold mono, order_rel, R_sets.
  intros W1 W2 HW.
  unfold repeat_break_f; intros a.
  apply bind_mono.
  + reflexivity.
  + intros x.
    destruct x.
    - apply HW.
    - reflexivity.
Qed.

Lemma repeat_break_f_continuous:
  forall {A B: Type}
         (body: A -> SetMonad.M (ContinueOrBreak A B)),
  continuous (repeat_break_f body).
Proof.
  intros.
  unfold continuous.
  unfold_CPO_defs.
  intros l _.
  unfold repeat_break_f;
  unfold bind, set_monad, SetMonad.bind; sets_unfold.
  intros a b.
  split.
  + intros [[a0 | b0] [? ?]].
    - destruct H0 as [i ?].
      exists i, (by_continue a0).
      tauto.
    - exists O, (by_break b0).
      tauto.
  + intros [i [[a0 | b0] [? ?]]].
    - exists (by_continue a0).
      split; [tauto |].
      exists i; tauto.
    - exists (by_break b0).
      split; [| tauto].
      tauto.
Qed.

Lemma repeat_break_unroll1:
  forall {A B: Type}
         (body: A -> SetMonad.M (ContinueOrBreak A B))
         (a: A),
    repeat_break body a ==
    x <- body a;;
    match x with
    | by_continue a' => repeat_break body a'
    | by_break b => ret b
    end.
Proof.
  intros.
  symmetry.
  apply (Kleene_LFix_is_fix
               (repeat_break_f body)
               (repeat_break_f_mono _)
               (repeat_break_f_continuous _)).
Qed.

(** 下面还可以定义循环体中的continue语句和break语句。*)

Definition continue {A B: Type} (a: A):
  SetMonad.M (ContinueOrBreak A B) :=
  ret (by_continue a).

Definition break {A B: Type} (b: B):
  SetMonad.M (ContinueOrBreak A B) :=
  ret (by_break b).

End SetMonadOperator1.

(** * 单子上的霍尔逻辑 *)

Module SetMonadHoare.
Import SetMonadOperator0
       SetMonadOperator1.


(** 集合单子上，霍尔三元组会退化为霍尔二元组。*)

Definition Hoare {A: Type} (c: SetMonad.M A) (P: A -> Prop): Prop :=
  forall a, a ∈ c -> P a.

(** 可以证明，各个单子算子满足下面性质。*)

Theorem Hoare_bind {A B: Type}:
  forall (f: SetMonad.M A)
         (g: A -> SetMonad.M B)
         (P: A -> Prop)
         (Q: B -> Prop),
    Hoare f P ->
    (forall a, P a -> Hoare (g a) Q) ->
    Hoare (bind f g) Q.
Proof.
  intros.
  unfold Hoare; sets_unfold;
  unfold bind, set_monad, SetMonad.bind.
  intros b [a [? ?]].
  specialize (H _ H1).
  specialize (H0 _ H _ H2).
  apply H0.
Qed.

Theorem Hoare_ret {A: Type}:
  forall (a: A) (P: A -> Prop),
    P a -> Hoare (ret a) P.
Proof.
  intros.
  unfold Hoare, ret, set_monad, SetMonad.ret; sets_unfold.
  intros.
  rewrite <- H0; tauto.
Qed.

Theorem Hoare_conseq {A: Type}:
  forall (f: SetMonad.M A) (P Q: A -> Prop),
    (forall a, P a -> Q a) ->
    Hoare f P ->
    Hoare f Q.
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.

Theorem Hoare_conjunct {A: Type}:
  forall (f: SetMonad.M A) (P Q: A -> Prop),
    Hoare f P ->
    Hoare f Q ->
    Hoare f (fun a => P a /\ Q a).
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.

Theorem Hoare_choice {A: Type}:
  forall (f g: SetMonad.M A)
         (P: A -> Prop),
    Hoare f P ->
    Hoare g P ->
    Hoare (choice f g) P.
Proof.
  intros.
  unfold Hoare; sets_unfold; unfold choice; Sets_unfold.
  intros.
  destruct H1; [apply H | apply H0]; tauto.
Qed.

Theorem Hoare_test_bind {A: Type}:
  forall (P: Prop)
         (f: SetMonad.M A)
         (Q: A -> Prop),
    (P -> Hoare f Q) ->
    (Hoare (test P;; f) Q).
Proof.
  intros.
  apply (Hoare_bind _ _ (fun _ => P)).
  + unfold Hoare, test; sets_unfold.
    tauto.
  + tauto.
Qed.

Theorem Hoare_repeat_break {A B: Type}:
  forall (body: A -> SetMonad.M (ContinueOrBreak A B))
         (P: A -> Prop)
         (Q: B -> Prop),
    (forall a, P a ->
               Hoare (body a) (fun x => match x with
                                        | by_continue a => P a
                                        | by_break b => Q b
                                        end)) ->
    (forall a, P a -> Hoare (repeat_break body a) Q).
Proof.
  intros.
  unfold Hoare; sets_unfold.
  intros b.
  unfold repeat_break, Kleene_LFix; unfold_CPO_defs.
  intros [n ?].
  revert a H0 b H1.
  change (forall a, P a -> Hoare (Nat.iter n (repeat_break_f body) ∅ a) Q).
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold repeat_break_f at 1.
    eapply Hoare_bind.
    - apply H, H0.
    - intros [a0 | b0].
      * apply IHn.
      * apply Hoare_ret.
Qed.

End SetMonadHoare.

Module SetMonadExamples3.
Import SetMonadHoare
       SetMonadOperator0
       SetMonadOperator1.

(** * 程序验证案例一：3x + 1 *)

Definition body_3x1 (x: Z): SetMonad.M (ContinueOrBreak Z Z) :=
  choice
    (test (x <= 1);; break x)
    (choice
      (test (exists k, x = 2 * k);;
       continue (x / 2))
      (test (exists k, k <> 0 /\ x = 2 * k + 1);;
       continue (3 * x + 1))).

Definition run_3x1: Z -> SetMonad.M Z :=
  repeat_break body_3x1.

Theorem functional_correctness_3x1:
  forall n: Z,
    n >= 1 ->
    Hoare (run_3x1 n) (fun m => m = 1).
Proof.
  apply Hoare_repeat_break.
  intros.
  unfold body_3x1.
  repeat apply Hoare_choice.
  + apply Hoare_test_bind.
    intros.
    apply Hoare_ret.
    lia.
  + apply Hoare_test_bind.
    intros.
    apply Hoare_ret.
    destruct H0 as [? ?].
    subst a.
    rewrite Z.mul_comm, Z_div_mult_full by lia.
    lia.
  + apply Hoare_test_bind.
    intros.
    apply Hoare_ret.
    lia.
Qed.

(** * 程序验证案例二：二分查找 *)

Definition body_binary_search (P: Z -> Prop):
  Z * Z -> SetMonad.M (ContinueOrBreak (Z * Z) Z) :=
  fun '(lo, hi) =>
  choice
    (test (lo + 1 = hi);; break lo)
    (test (lo + 1 < hi);;
     let mid := (lo + hi) / 2 in
     choice
       (test (P mid);; continue (mid, hi))
       (test (~ P mid);; continue (lo, mid))).

Definition binary_search (P: Z -> Prop) (lo hi: Z):
  SetMonad.M Z :=
  repeat_break (body_binary_search P) (lo, hi).

Theorem functional_correctness_binary_search:
  forall (P: Z -> Prop) lo hi,
    (forall n m, n <= m -> P m -> P n) ->
    P lo ->
    ~ P hi ->
    Hoare (binary_search P lo hi)
          (fun x => P x /\ ~ P (x + 1)).
Proof.
  intros.
  apply (Hoare_repeat_break _
           (fun '(lo, hi) => P lo /\ ~ P hi)); [| tauto].
  clear lo hi H0 H1.
  intros [lo hi] [? ?].
  unfold body_binary_search.
  apply Hoare_choice.
  + apply Hoare_test_bind.
    intros.
    apply Hoare_ret.
    subst hi; tauto.
  + apply Hoare_test_bind.
    intros.
    apply Hoare_choice; apply Hoare_test_bind; intros.
    - apply Hoare_ret.
      tauto.
    - apply Hoare_ret.
      tauto.
Qed.

End SetMonadExamples3.

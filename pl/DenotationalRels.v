Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.InductiveType.
Require Import PL.RecurProp.
Require Import PL.Syntax.
Require Import PL.DenotationalBasic.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.




(** * 在Coq中表示集合与二元关系 *)

(** SetsClass拓展库中提供了有关集合的一系列定义。例如：
   
    - 空集：用 _[∅]_ 或者一堆方括号表示，定义为_[Sets.empty]_；

    - 全集：定义为_[Sets.full]_（全集没有专门的表示符号）；

    - 单元集：用一对方括号表示，定义为_[Sets.singleton]_；

    - 补集：定义为_[Sets.complement]_（补集没有专门的表示符号）；

    - 并集：用_[∪]_表示，定义为_[Sets.union]_；

    - 交集：用_[∩]_表示，定义为_[Sets.intersect]_；

    - 集合相等：用_[==]_表示，定义为_[Sets.equiv]_；

    - 元素与集合关系：用_[∈]_表示，定义为_[Sets.In]_；

    - 子集关系：用_[⊆]_表示，定义为_[Sets.included]_；

    在这些符号中，补集以及其他Coq函数的优先级最高，交集的优先级其次，并集的优先级再次，
    集合相等、集合包含与属于号的优先级最低。

    SetsClass拓展库中提供了这些关于二元关系的定义：
   
    - 二元关系的连接：用 _[∘]_表示，定义为_[Rels.concat]_；

    - 相等关系：定义为_[Rels.id]_（没有专门的表示符号）；

    - 测试：定义为_[Rels.test]_（没有专门的表示符号）。

    基于此，我们可以将一些二元关系运算的例子写作Coq命题，下面就是一个这样的例子。*)

Fact plus_1_concat_plus_1:
  forall S1 S2: Z -> Z -> Prop,
    (forall n m, (n, m) ∈ S1 <-> m = n + 1) ->
    (forall n m, (n, m) ∈ S2 <-> m = n + 2) ->
    S1 ∘ S1 == S2.
Proof.
  intros S1 S2 H_S1 H_S2.
  Sets_unfold.
  intros x z.
  (** _[Sets_unfold]_指令将_[∘]_的定义展开，现在需要证明：
        - exists y, (x, y) ∈ S1 /\ (y, z) ∈ S1
      当且仅当
        - (x, z) ∈ S2]_。*)
  rewrite H_S2.
  setoid_rewrite H_S1.
  (** 根据_[S1]_与_[S2]_的定义，就只需要证明：
        _[(exists y, y = x + 1 /\ z = y + 1) <-> z = x + 2]_ *)
  split.
  + intros [y [? ?]].
    lia.
  + intros.
    exists (x + 1).
    lia.
Qed.

(** * Coq中定义程序语句的指称语义 *)

Module DntSem_SimpleWhile3.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2.

Record asgn_sem
         (X: var_name)
         (D: state -> Z)
         (s1 s2: state): Prop :=
  {
    asgn_sem_asgn_var: s2 X = D s1;
    asgn_sem_other_var: forall Y, X <> Y -> s2 Y = s1 Y;
  }.

Notation "H '.(asgn_sem_asgn_var)'" :=
  (asgn_sem_asgn_var _ _ _ _ H)
  (at level 1).

Notation "H '.(asgn_sem_other_var)'" :=
  (asgn_sem_other_var _ _ _ _ H)
  (at level 1).


Definition skip_sem: state -> state -> Prop :=
  Rels.id.

Definition seq_sem (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  D1 ∘ D2.

Definition test_true
             (D: state -> bool):
  state -> state -> Prop :=
  Rels.test (fun s => D s = true).

Definition test_false
             (D: state -> bool):
  state -> state -> Prop :=
  Rels.test (fun s => D s = false).

Definition if_sem
             (D0: state -> bool)
             (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  (test_true D0 ∘ D1) ∪ (test_false D0 ∘ D2).

Fixpoint iterLB
           (D0: state -> bool)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => test_false D0
  | S n0 => test_true D0 ∘ D1 ∘ iterLB D0 D1 n0
  end.

Module WhileSem1.

(** 第一种定义方式 *)
Definition while_sem
             (D0: state -> bool)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (iterLB D0 D1).

End WhileSem1.

Fixpoint boundedLB
           (D0: state -> bool)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1 ∘ boundedLB D0 D1 n0) ∪
      (test_false D0)
  end.

Module WhileSem2.

(** 第二种定义方式 *)
Definition while_sem
             (D0: state -> bool)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (boundedLB D0 D1).

End WhileSem2.

(** 我们选择第二种定义。*)

Export WhileSem2.


(** 下面是程序语句指称语义的递归定义。*)

Fixpoint eval_com (c: com): state -> state -> Prop :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr_int e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr_bool e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr_bool e) (eval_com c1)
  end.

Notation "⟦ c ⟧" := (eval_com c)
  (at level 0, only printing, c custom prog_lang_entry at level 99).

Ltac get_prog_syntax x ::=
  match type of x with
  | expr_int => constr:(x)
  | Z => constr:(EConst x)
  | string => constr:(EVar' x)
  | var_name => constr:(EVar x)
  | expr_bool => constr:(x)
  | com => constr:(x)
  end.

Ltac any_eval' x ::=
  match goal with
  | |- _ -> Z    => exact (eval_expr_int x)
  | |- _ -> bool => exact (eval_expr_bool x)
  | |- _ -> Prop => exact (eval_com x)
  | _            =>
    match type of x with
    | expr_int  => exact (eval_expr_int x)
    | expr_bool => exact (eval_expr_bool x)
    | com       => exact (eval_com x)
    end
  end.

Ltac unfold_com_sem :=
  cbv [seq_sem if_sem while_sem skip_sem].

Ltac unfold_com_sem_in_hyp H :=
  cbv [seq_sem if_sem while_sem skip_sem] in H.

Ltac ___unfold_sem ::=
  simpl eval_com; simpl eval_expr_bool; simpl eval_expr_int;
  unfold_com_sem; unfold_expr_bool_sem; unfold_expr_int_sem.

Ltac ___unfold_sem_in_hyp H ::=
  simpl eval_com in H;
  simpl eval_expr_bool in H;
  simpl eval_expr_int in H;
  unfold_com_sem_in_hyp H;
  unfold_expr_bool_sem_in_hyp H;
  unfold_expr_int_sem_in_hyp H.

Ltac unfold_sem1_tac T :=
  match T with
  | context G [eval_com (CIf ?e ?c1 ?c2)] =>
      let if_sem' := eval cbv [if_sem] in if_sem in
      let ret := eval cbv beta iota in (if_sem' ⟦ e ⟧ ⟦ c1 ⟧ ⟦ c2 ⟧) in
      let T' := context G [ret] in
      T'
  | context G [eval_com (CSeq ?c1 ?c2)] =>
      let seq_sem' := eval cbv [seq_sem] in seq_sem in
      let ret := eval cbv beta iota in (seq_sem' ⟦ c1 ⟧ ⟦ c2 ⟧) in
      let T' := context G [ret] in
      T'
  end.

Ltac unfold_sem1_in_hypo_tac H :=
  match type of H with
  | ?T => let T' := unfold_sem1_tac T in
          change T' in H
  end.

Tactic Notation "unfold_sem1" "in" constr(H) :=
  unfold_sem1_in_hypo_tac H.


End DntSem_SimpleWhile3.

(** * 集合、关系与逻辑命题的Coq证明 *)

(** ** 集合命题的基本证明方法 *)

(** _[Sets_unfold]_指令可以将集合的性质转化为逻辑命题。 *)

Theorem Sets1_intersect_included1: forall A (X Y: A -> Prop),
  X ∩ Y ⊆ X.
Proof.
  intros.
  (** 下面一条命令_[Sets_unfold]_是SetsClass库提供的自动证明指令，它可以将有关
      集合的性质转化为有关命题的性质。*)
  Sets_unfold.
  (** 原本要证明的关于交集的性质现在就转化为了：
        _[forall a : A, a ∈ X /\ a ∈ Y -> a ∈ X]_
      这个关于逻辑的命题在Coq中是容易证明的。*)
  intros.
  tauto.
Qed.

Lemma Sets1_included_union1: forall A (X Y: A -> Prop),
  X ⊆ X ∪ Y.
Proof.
  intros.
  Sets_unfold.
  (** 经过转化，要证明的结论是：_[forall a : A, a ∈ X -> a ∈ X \/ a ∈ Y]_。*)
  intros.
  tauto.
Qed.

Example Sets2_proof_sample1: forall A B (X Y Z: A -> B -> Prop),
  X ∪ Y ⊆ Z ->
  Y ⊆ Z.
Proof.
  intros.
  Sets_unfold in H.
  Sets_unfold.
  intros a b.
  specialize (H a b).
  tauto.
Qed.


(** 集合相等是一个等价关系，集合包含具有自反性和传递性。集合间的交集、并集和补集运算保
    持“包含”与“被包含”关系，也会保持集合相等关系。SetsClass拓展库提供了这些性质的证
    明，从而支持利用_[rewrite]_指令证明集合性质。*)

Example Sets1_proof_sample2: forall (A: Type) (X Y Z: A -> Prop),
  X == Y -> X == Z -> Y == Z.
Proof.
  intros.
  rewrite <- H, <- H0.
  reflexivity.
Qed.

Example Sets1_proof_sample3: forall (A: Type) (F: (A -> Prop) -> (A -> Prop)),
  (forall X: A -> Prop, X ⊆ F X) ->
  (forall X: A -> Prop, X ⊆ F (F X)).
Proof.
  intros.
  rewrite <- H, <- H.
  reflexivity.
Qed.

Example Sets1_proof_sample4: forall (A: Type) (X1 X2 Y1 Y2: A -> Prop),
  X1 == X2 -> Y1 ⊆ Y2 -> X1 ∪ Y1 ⊆ X2 ∪ Y2.
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.


(** ** 交集与并集性质的Coq证明 *)

(** 证明集合相等的方法： 
   
        Sets_equiv_Sets_included:
          forall x y, x == y <-> x ⊆ y /\ y ⊆ x
      

    证明交集有关的性质： 

        _[x ⊆ y ∩ z]_可以被规约为_[x ⊆ y]_与_[x ⊆ z]_; 

        _[x ∩ y ⊆ z]_可以被规约为_[x ⊆ z]_; 

        _[x ∩ y ⊆ z]_也可以被规约为_[y ⊆ z]_。 

    在Coq中，前一种证明可以通过_[apply]_下面引理实现。
   
        Sets_included_intersect:
          forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z
      
    而后两种证明可以通过_[rewrite]_下面引理实现。
   
        Sets_intersect_included1:
          forall x y, x ∩ y ⊆ x
        Sets_intersect_included2:
          forall x y, x ∩ y ⊆ y
      
    例如，我们可以如下证明集合交具有交换律和结合律。*)

Theorem Sets1_intersect_comm:
  forall {A: Type} (x y: A -> Prop),
    x ∩ y == y ∩ x.
Proof.
  intros.
  (** 首先，要证明两个集合相等只需要证明它们互为子集。*)
  apply Sets_equiv_Sets_included; split.
  + (** 第一个分支需要证明_[x ∩ y ⊆ y ∩ x]_，右边是两个集合的交集，因此这两个集合都包
        含左边集合即可。*)
    apply Sets_included_intersect.
    - (** 现在需要证明_[x ∩ y ⊆ y]_，形式上，是要证明左侧两个集合的交集是右侧集合的子
          集，这只需要证明左侧的第二个集合是右侧集合的子集就够了。 *)
      rewrite Sets_intersect_included2.
      reflexivity.
    - (** 类似的，这个子分支需要证明_[x ∩ y ⊆ x]_，我们可以选择将其归结为证明左边的一
          个集合是右边集合的子集。。 *)
      rewrite Sets_intersect_included1.
      reflexivity.
  + (** 第二个分支的证明是类似的。*)
    apply Sets_included_intersect.
    - rewrite Sets_intersect_included2.
      reflexivity.
    - rewrite Sets_intersect_included1.
      reflexivity.
Qed.

Theorem Sets1_intersect_assoc:
  forall {A: Type} (x y z: A -> Prop),
    (x ∩ y) ∩ z == x ∩ (y ∩ z).
Proof.
  intros.
  (** 与证明交集交换律的时候类似，我们将两个集合相等的证明归于为证明它们互为子集。*)
  apply Sets_equiv_Sets_included; split.
  + (** 第一个分支需要证明_[(x ∩ y) ∩ z ⊆ x ∩ (y ∩ z)]_。要证明左侧是右侧三个集合交集
        的子集，就需要证明左侧是右侧每一个集合的子集。*)
    apply Sets_included_intersect; [| apply Sets_included_intersect].
    (** 现在三个证明目标分别是：
        - (x ∩ y) ∩ z ⊆ x
        - (x ∩ y) ∩ z ⊆ y
        - (x ∩ y) ∩ z ⊆ z
        证明时只需要指明左边三个集合中哪一个是右边的子集即可。*)
    - rewrite Sets_intersect_included1.
      rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included1.
      rewrite Sets_intersect_included2.
      reflexivity.
    - rewrite Sets_intersect_included2.
      reflexivity.
  + (** 第二个分支的证明是类似的。*)
    apply Sets_included_intersect; [apply Sets_included_intersect |].
    - rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included2.
      rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included2.
      rewrite Sets_intersect_included2.
      reflexivity.
Qed.


(** 证明并集有关的性质： 

        _[x ⊆ y ∪ z]_可以被规约为_[x ⊆ y]_; 

        _[x ⊆ y ∪ z]_也可以被规约为_[x ⊆ z]_; 

        _[x ∪ y ⊆ z]_可以被规约为_[x ⊆ z]_与_[y ⊆ z]_。 

    在Coq中，前两种证明可以通过从右向左_[rewrite]_下面引理实现。
   
        Sets_included_union1:
          forall x y, x ⊆ x ∪ y
        Sets_included_union2:
          forall x y, y ⊆ x ∪ y
      
    而后一种证明则可以通过_[apply]_下面引理实现。
   
        Sets_union_included:
          forall x y z, x ⊆ z -> y ⊆ z -> x ∪ y ⊆ z;
      
    有时，包含号_[⊆]_左侧的集合不是一个并集，需要先使用交集对于并集的分配律才能使用
    _[Sets_union_included]_。*)

(************)
(** 习题：  *)
(************)

(** 请证明下面集合运算的性质。*)

Example Sets1_intersect_absorb_union:
  forall {A: Type} (x y: A -> Prop),
    x ∩ (x ∪ y) == x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面集合运算的性质。*)

Example Sets1_union_absorb_intersect:
  forall {A: Type} (x y: A -> Prop),
    x ∪ (x ∩ y) == x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 基本证明方法汇总：
   
        Sets_equiv_Sets_included:
          forall x y, x == y <-> x ⊆ y /\ y ⊆ x
        Sets_intersect_included1:
          forall x y, x ∩ y ⊆ x
        Sets_intersect_included2:
          forall x y, x ∩ y ⊆ y
        Sets_included_intersect:
          forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z
        Sets_included_union1:
          forall x y, x ⊆ x ∪ y
        Sets_included_union2:
          forall x y, y ⊆ x ∪ y
        Sets_union_included:
          forall x y z, x ⊆ z -> y ⊆ z -> x ∪ y ⊆ z
        Sets_intersect_union_distr_r:
          forall x y z, (x ∪ y) ∩ z == x ∩ z ∪ y ∩ z
        Sets_intersect_union_distr_l:
          forall x y z, x ∩ (y ∪ z) == x ∩ y ∪ x ∩ z
      

    其他常用性质汇总：
   
        Sets_intersect_comm:
          forall x y, x ∩ y == y ∩ x
        Sets_intersect_assoc:
          forall x y z, (x ∩ y) ∩ z == x ∩ (y ∩ z)
        Sets_union_comm:
          forall x y, x ∪ y == y ∪ x
        Sets_union_assoc:
          forall x y z, (x ∪ y) ∪ z == x ∪ (y ∪ z)
        Sets_union_intersect_distr_l:
          forall x y z, x ∪ (y ∩ z) == (x ∪ y) ∩ (x ∪ z)
        Sets_union_intersect_distr_r:
          forall x y z, (x ∩ y) ∪ z == (x ∪ z) ∩ (y ∪ z)
      *)


(** ** 空集、全集、无穷交与无穷并性质的Coq证明 *)

(** SetsClass拓展库对于空集的支持主要是通过以下性质：空集是一切集合的子集。
   
        Sets_empty_included: forall x, ∅ ⊆ x
      

    相对应的，一切集合都是全集的子集。 
   
        Sets_included_full: forall x, x ⊆ Sets.full
      
    基于这两条性质，可以证明许多有用的导出性质。SetsClass提供的导出性质有：
   
        Sets_union_empty_l: forall x, ∅ ∪ x == x
        Sets_union_empty_r: forall x, x ∪ ∅ == x
        Sets_intersect_empty_l: forall x, ∅ ∩ x == ∅
        Sets_intersect_empty_r: forall x, x ∩ ∅ == ∅
        Sets_union_full_l: forall x, Sets.full ∪ x == Sets.full
        Sets_union_full_r: forall x, x ∪ Sets.full == Sets.full
        Sets_intersect_full_l: forall x, Sets.full ∩ x == x
        Sets_intersect_full_r: forall x, x ∩ Sets.full == x
        Sets_equiv_empty_fact: forall x, x ⊆ ∅ <-> x == ∅
        Sets_equiv_full_fact: forall x, Sets.full ⊆ x <-> x == Sets.full
      *)

(************)
(** 习题：  *)
(************)

(** 前面已经提到，SetsClass拓展库已经证明了_[Sets_intersect_empty_l]_。请你只使用
    _[Sets_empty_included]_以及交集的性质证明它。*)

Lemma Sets1_intersect_empty_l:
  forall (A: Type) (x: A -> Prop), ∅ ∩ x == ∅.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** SetsClass拓展库提供了两种支持无穷交集和无穷并集的定义。它们的证明方式与普通的并集
    与交集的证明方式是类似的。

    - 基于指标集的集合并：_[⋃ X]_，_[Sets.indexed_union X]_
    
    - 基于指标集的集合交：_[⋂ X]_，_[Sets.indexed_intersect X]_
    
    - 广义并：_[⨆ U]_，_[Sets.general_union U]_
    
    - 广义交：_[⨅ U]_，_[Sets.general_intersect U]_
*)

Example Sets1_union_indexed_intersect_fact:
  forall {A: Type} (x: nat -> A -> Prop) (y: A -> Prop),
    (⋂ x) ∪ y ⊆ ⋂ (fun n => x n ∪ y).
Proof.
  intros.
  (** 要证明左边集合是右边这无穷多个集合交集的子集，就需要证明左边集合是右边每一个集合
      的子集。 *)
  apply Sets_included_indexed_intersect.
  intros n.
  (** 现在只需要证明_[⋂ x ∪ y ⊆ x n ∪ y]_。 *)
  rewrite (Sets_indexed_intersect_included n).
  reflexivity.
Qed.

(** ** 逻辑命题的Coq证明 *)

(** 下面是证明“并且”、“或”与“当且仅当”时常用的证明指令汇总与拓展。 *)


(** ** 二元关系运算性质的Coq证明 *)

(** 二元关系的运算性质： 
   

    - 结合律：_[(x ∘ y) ∘ z == x ∘ (y ∘ z)]_
    
    - 左单位元：_[Rels.id ∘ x == x]_
    
    - 右单位元：_[x ∘ Rels.id == x]_
    
    - 左分配律：_[x ∘ (y ∪ z) == x ∘ y ∪ x ∘ z]_

    - 右分配律：_[(x ∪ y) ∘ z == x ∘ z ∪ y ∘ z]_


    另外，二元关系对并集的分配律对于无穷并集也成立。这些性质对应了SetsClass库中的下面
    这些定理。*)
(************)
(** 习题：  *)
(************)

(** 请根据二元关系连接的定义证明下面性质。*)

Lemma plus_n_plus_m:
  forall (plus_rel: Z -> Z -> Z -> Prop),
    (forall n m1 m2, (m1, m2) ∈ plus_rel n <-> m1 + n = m2) ->
    (forall n m, plus_rel n ∘ plus_rel m == plus_rel (n + m)).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请根据二元关系连接的定义证明下面性质。*)

Lemma Rels22_concat_assoc:
  forall {A: Type} (x y z: A -> A -> Prop),
    (x ∘ y) ∘ z == x ∘ (y ∘ z).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma Rels22_concat_id_l:
  forall {A: Type} (x: A -> A -> Prop),
    Rels.id ∘ x == x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma Rels22_concat_union_distr_r:
  forall {A: Type} (x y z: A -> A -> Prop),
    (x ∪ y) ∘ z == x ∘ z ∪ y ∘ z.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** * 程序语句指称语义的性质 *)

Module DntSem_SimpleWhile3_Properties.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3.

(** 下面是一些关于语义算子和指称语义的例子。首先，根据_[test_true]_、_[test_false]_
    以及测试关系的定义，我们知道_[test_true ⟦ "x" < 10 ⟧]_中只包含变量x取值小于10的
    所有程序状态。*)

Example lt10_is_true_fact: 
  (fun s => ⟦ "x" < 10 ⟧ s = true) ==
  (fun s => s "x" < 10).
Proof.
  sets_unfold.
  intros s.
  rewrite lt_spec.
  unfold_sem.
  tauto.
Qed.

Example lt10_test_true_fact:
  forall s1 s2: state,
    (s1, s2) ∈ test_true (⟦ "x" < 10 ⟧) <->
    s1 "x" < 10 /\ s1 = s2.
Proof.
  unfold test_true.
  sets_unfold.
  intros s1 s2.
  rewrite lt_spec.
  unfold_sem.
  tauto.
Qed.

(** 能否用_[lt10_is_true_fact]_证明_[lt10_test_true_fact]_呢？可以！*)

Example lt10_test_true_fact___again:
  forall s1 s2: state,
    (s1, s2) ∈ test_true (⟦ "x" < 10 ⟧) <->
    s1 "x" < 10 /\ s1 = s2.
Proof.
  unfold test_true.
  intros s1 s2.
  rewrite lt10_is_true_fact.
  sets_unfold.
  tauto.
Qed.

(** 其次，由于x < x + 1这个布尔表达式恒为真，所以它对应的_[test_true]_关系是相等关
    系，它对应的_[test_false]_关系是空关系。*)

Example lt_plus_one_is_true_fact: 
  (fun s => ⟦ "x" < "x" + 1 ⟧ s = true) ==
  Sets.full.
Proof.
  sets_unfold.
  intros s.
  rewrite lt_plus_one_fact.
  unfold_sem.
  tauto.
Qed.

Example lt_plus_one_is_false_fact: 
  (fun s => ⟦ "x" < "x" + 1 ⟧ s = false) == ∅.
Proof.
  sets_unfold.
  intros s.
  rewrite lt_plus_one_fact.
  unfold_sem.
  intuition.
Qed.

Example lt_plus_one_test_true_fact: 
  test_true (⟦ "x" < "x" + 1 ⟧) == Rels.id.
Proof.
  unfold test_true.
  rewrite lt_plus_one_is_true_fact.
  apply Rels_test_full.
Qed.

Example lt_plus_one_test_false_fact: 
  test_false (⟦ "x" < "x" + 1 ⟧) == ∅.
Proof.
  unfold test_false.
  rewrite lt_plus_one_is_false_fact.
  apply Rels_test_empty.
Qed.

(** 下面这个例子描述了一条简单赋值语句的性质。*)

Example inc_x_fact:
  forall s1 s2 n,
    (s1, s2) ∈ ⟦ "x" = "x" + 1 ⟧ ->
    s1 "x" = n ->
    s2 "x" = n + 1.
Proof.
  intros.
  unfold_sem in H.
  pose proof H.(asgn_sem_asgn_var) as H1; simpl in H1.
  lia.
Qed.

(** 下面这个例子描述了一条条件分支语句的性质。我们在第一次证明它的时候主要会使用
    _[Sets_unfold1]_指令和_[unfold_sem1]_指令，分别表示将集合运算的定义展开一层，以
    及将程序语句语义的定义展开一层。*)

Example abs_neg_5_fact:
  forall s1 s2,
    (s1, s2) ∈ ⟦ if ("x" < 0)
                 then { "y" = 0 - "x" }
                 else { "y" = "x" } ⟧ ->
    s1 "x" = -5 ->
    s2 "y" = 5.
Proof.
  intros.
  (** 首先展开if语句的语义定义。*)
  unfold_sem1 in H.
  Sets_unfold1 in H.
  (** 现在，关于程序语义的前提已经展开为：
      - H: (s1, s2) ∈ test_true ⟦ "x" < 0 ⟧ ∘
                      ⟦ "x" = 0 - "x" ⟧ \/
           (s1, s2) ∈ test_false ⟦ "x" < 0 ⟧ ∘
                      ⟦ skip ⟧
      因此可以进行分类讨论。*)
  destruct H.
  + (** 执行if-then分支的情况 *)
    Sets_unfold1 in H.
    destruct H as [s1' [? ?] ].
    (** 根据_[∘]_的定义，我们知道，存在_[s1']_使得
        - H: (s1, s1') ∈ test_true ⟦ "x" < 0 ⟧
        - H1: (s1', s2) ∈ ⟦ "x" = 0 - "x" ⟧ *)
    unfold test_true in H; Sets_unfold1 in H.
    (** 根据_[test_true]_的定义，我们知道_[s1 = s1']_。*)
    destruct H as [_ ?]; subst s1'.
    (** 现在，所有_[s1']_全部被替换为_[s1]_了，更新后的_[H1]_是：
        - H1: (s1, s2) ∈ ⟦ "x" = 0 - "x" ⟧
        下面只需要利用赋值语句的语义证明结论就可以了。 *)
    pose proof H1.(asgn_sem_asgn_var).
    unfold_sem in H.
    lia.
  + (** 执行if-else分支的情况 *)
    Sets_unfold1 in H.
    destruct H as [s1' [? ?] ].
    (** 根据_[∘]_的定义，我们知道，存在_[s1']_使得
        - H: (s1, s1') ∈ test_false ⟦ "x" < 0 ⟧
        - H1: (s1', s2) ∈ ⟦ skip ⟧
        这一个分支的证明中就只需要利用_[H]_和另一个前提_[s1 "x" = 5]_推出矛盾即可。 *)
    unfold test_false in H; Sets_unfold1 in H.
    destruct H as [? _].
    (** 利用_[test_false]_的定义，我们知道
        - ⟦ "x" < 0 ⟧ s1 = false
        这个分支中，我们就不需要使用_[s1 = s1']_这个条件了。*)
    unfold_sem in H.
    rewrite H0 in H; simpl in H.
    discriminate H.
Qed.

(** 在上面证明中，有这样一些有用的证明模式：

    - 遇到形如_[(s1, s2) ∈ ⟦ if (...) then { ... } else { ... } ⟧]_或形如
      _[(s1, s2) ∈ R1 ∪ R2]_的前提时，可以对其分类讨论；

    - 遇到形如_[(s1, s2) ∈ ⟦ ... ; ... ⟧]_或形如_[(s1, s2) ∈ R1 ∘ R2]_的前提时，可
      以将其拆解为两个步骤的信息；

    - 遇到形如_[(s1, s2) ∈ test_true (...)]_或_[(s1, s2) ∈ test_false (...)]_的前
      提时，可以得到_[s1]_上布尔表达式求值的真假，并推断出_[s1 = s2]_。

    下面我们引入_[destruct_union]_、_[destruct_concat]_两条集成证明指令来简化证明。*)

Ltac destruct_Sets_union_tac H H1 H2 :=
  match type of H with
  | (?s1, ?s2) ∈ ?R1 ∪ ?R2 =>
      change ((s1, s2) ∈ R1 \/ (s1, s2) ∈ R2) in H;
      destruct H as [H1 | H2]
  | (?s1, ?s2) ∈ if_sem ?D0 ?D1 ?D2 =>
      change ((s1, s2) ∈ test_true D0 ∘ D1 \/ 
              (s1, s2) ∈ test_false D0 ∘ D2) in H;
      destruct H as [H1 | H2]
  | (?s1, ?s2) ∈ eval_com (CIf ?e ?c1 ?c2) =>
      change ((s1, s2) ∈ test_true ⟦ e ⟧ ∘ ⟦ c1 ⟧ \/ 
              (s1, s2) ∈ test_false ⟦ e ⟧ ∘ ⟦ c2 ⟧) in H;
      destruct H as [H1 | H2]
  end.

Ltac destruct_Rels_concat_tac H x H1 H2 :=
  match type of H with
  | (?s1, ?s2) ∈ ?R1 ∘ ?R2 =>
      change (exists x0, (s1, x0) ∈ R1 /\ (x0, s2) ∈ R2) in H;
      destruct H as [x [H1 H2] ]
  | (?s1, ?s2) ∈ seq_sem ?R1 ?R2 =>
      change (exists x0, (s1, x0) ∈ R1 /\ (x0, s2) ∈ R2) in H;
      destruct H as [x [H1 H2] ]
  | (?s1, ?s2) ∈ eval_com (CSeq ?c1 ?c2) =>
      change (exists x0, (s1, x0) ∈ ⟦ c1 ⟧ /\ (x0, s2) ∈ ⟦ c2 ⟧) in H;
      destruct H as [x [H1 H2] ]
  end.

Ltac destruct_Rels_concat_test_tac H H1 H2 :=
  match type of H with
  | (?s1, ?s2) ∈ test_true ?X ∘ ?R2 =>
      let s := fresh "s" in
      let H0 := fresh "H" in
      change (exists s, (X s1 = true /\ s1 = s) /\ (s, s2) ∈ R2) in H;
      destruct H as [s [ [H1 H0] H2] ];
      subst s;
      try apply lt_spec in H1
  | (?s1, ?s2) ∈ test_false ?X ∘ ?R2 =>
      let s := fresh "s" in
      let H0 := fresh "H" in
      change (exists s, (X s1 = false /\ s1 = s) /\ (s, s2) ∈ R2) in H;
      destruct H as [s [ [H1 H0] H2] ];
      subst s;
      try (rewrite <- Bool.not_true_iff_false in H1;
           rewrite lt_spec in H1)
  end.

Tactic Notation "destruct_union" constr(H) "as" "[" simple_intropattern(H1) "|" simple_intropattern(H2) "]" :=
  destruct_Sets_union_tac H H1 H2.

Tactic Notation "destruct_concat" constr(H) "as" "[" simple_intropattern(x) simple_intropattern(H1) simple_intropattern(H2) "]" :=
  destruct_Rels_concat_tac H x H1 H2.

Tactic Notation "destruct_concat" constr(H) "as" "[" simple_intropattern(H1) simple_intropattern(H2) "]" :=
  destruct_Rels_concat_test_tac H H1 H2.

(** 基于这些初步集成的指令，我们可以重新证明_[abs_neg_5_fact]_。*)

Example abs_neg_5_fact___again:
  forall s1 s2,
    (s1, s2) ∈ ⟦ if ("x" < 0)
                 then { "y" = 0 - "x" }
                 else { "y" = "x" } ⟧ ->
    s1 "x" = -5 ->
    s2 "y" = 5.
Proof.
  intros.
  destruct_union H as [H | H].
  + destruct_concat H as [_ H].
    pose proof H.(asgn_sem_asgn_var).
    unfold_sem in H1.
    lia.
  + destruct_concat H as [H _].
    unfold_sem in H.
    lia.
Qed.

(** 事实上，我们可以对这些证明步骤进一步集成，之后，我们也可以用
    - _[choose_if_then_branch]_
    - _[choose_if_else_branch]_
    这两条指令证明if语句的性质。*)

Ltac choose_if_then_branch H :=
  destruct_Sets_union_tac H H H;
  [
    destruct_concat H as [_ H]
  |
    destruct_concat H as [H _];
    try (unfold_sem in H; try lia)
  ].

Ltac choose_if_else_branch H :=
  destruct_Sets_union_tac H H H;
  [
    destruct_concat H as [H _];
    try (unfold_sem in H; try lia)
  |
    destruct_concat H as [_ H]
  ].

(** 下面我们再一次重新证明前面的例子。*)

Example abs_neg_5_fact___again2:
  forall s1 s2,
    (s1, s2) ∈ ⟦ if ("x" < 0)
                 then { "y" = 0 - "x" }
                 else { "y" = "x" } ⟧ ->
    s1 "x" = -5 ->
    s2 "y" = 5.
Proof.
  intros.
  choose_if_then_branch H.
  (** 此时，已经排除了if-else分支的可能性，并且已经导出：
      - H: (s1, s2) ∈ ⟦ "y" = 0 - "x" ⟧ *)
  pose proof H.(asgn_sem_asgn_var).
  unfold_sem in H1.
  lia.
Qed.

(** 下面是使用这些集成证明指令的另外两个例子。*)

Example if_lt_10_plus_one_fact0:
  forall s1 s2,
    (s1, s2) ∈ ⟦ if ("x" < 10)
                 then { "x" = "x" + 1 }
                 else { skip } ⟧ ->
    s1 "x" = 0 ->
    s2 "x" = 1.
Proof.
  intros.
  choose_if_then_branch H.
  pose proof H.(asgn_sem_asgn_var).
  unfold_sem in H1.
  lia.
Qed.

Example if_lt_10_plus_one_fact10:
  forall s1 s2,
    (s1, s2) ∈ ⟦ if ("x" < 10)
                 then { "x" = "x" + 1 }
                 else { skip } ⟧ ->
    s1 "x" = 10 ->
    s2 "x" = 10.
Proof.
  intros.
  choose_if_else_branch H.
  unfold_sem in H.
  sets_unfold in H.
  subst s2; lia.
Qed.

(** 下面证明几条程序语句语义的一般性性质。我们首先可以证明，两种while语句语义的定义方式
    是等价的。*)

Lemma while_sem1_while_sem2_equiv:
  forall D0 D1,
    WhileSem1.while_sem D0 D1 ==
    WhileSem2.while_sem D0 D1.
Proof.
  intros.
  unfold WhileSem1.while_sem, while_sem.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_indexed_union_included.
    intros n.
    rewrite <- (Sets_included_indexed_union (S n)).
    induction n; simpl.
    - Sets_unfold; intros; tauto.
    - rewrite IHn; simpl.
      Sets_unfold; intros; tauto.
  + apply Sets_indexed_union_included.
    intros n.
    induction n; simpl.
    - apply Sets_empty_included.
    - rewrite IHn.
      clear n IHn.
      apply Sets_union_included.
      * rewrite Rels_concat_indexed_union_distr_l.
        rewrite Rels_concat_indexed_union_distr_l.
        apply Sets_indexed_union_included.
        intros n.
        rewrite <- (Sets_included_indexed_union (S n)).
        simpl.
        reflexivity.
      * rewrite <- (Sets_included_indexed_union O).
        simpl.
        reflexivity.
Qed.

(** 还可以证明，_[boundedLB]_是递增的。*)

Lemma boundedLB_inc1: forall D0 D1 n,
  boundedLB D0 D1 n ⊆ boundedLB D0 D1 (S n).
Proof.
  intros.
  induction n; simpl.
  + apply Sets_empty_included.
  + rewrite IHn at 1.
    reflexivity.
Qed.

Theorem boundedLB_inc: forall D0 D1 n m,
  boundedLB D0 D1 m ⊆ boundedLB D0 D1 (n + m).
Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn.
    rewrite (boundedLB_inc1 D0 D1 (n + m)) at 1.
    simpl.
    reflexivity.
Qed.

(** 下面定义程序语句的行为等价。*)

Definition cequiv (c1 c2: com): Prop :=
  ⟦ c1 ⟧ == ⟦ c2 ⟧.

Notation "c1 '~=~' c2" := (cequiv c1 c2)
  (at level 69, no associativity, only printing).

Ltac any_equiv' x y ::=
  match type of x with
  | expr_int  => exact (iequiv x y)
  | expr_bool => exact (bequiv x y)
  | com       => exact (cequiv x y)
  | _         =>
      match type of y with
      | expr_int  => exact (iequiv x y)
      | expr_bool => exact (bequiv x y)
      | com       => exact (cequiv x y)
      end
  end.

(** 可以证明，赋值语句、顺序执行、if语句和while语句对应的语义算子_[asgn_sem]_、
    _[seq_sem]_、_[if_sem]_与_[while_sem]_能由相同的函数及集合计算得到相同的集合。其
    中，证明if语句和while语句性质时，需要先证明_[test_true]_和_[test_false]_能够由相
    同的函数计算得到相同的集合。*)

#[export] Instance asgn_sem_congr:
  Proper (eq ==> func_equiv _ _ ==> Sets.equiv) asgn_sem.
Proof.
  unfold Proper, respectful.
  intros x x' Hx D1 D2 H; subst x'.
  sets_unfold; intros s1 s2.
  split; intros; split.
  + rewrite <- H.
    apply H0.(asgn_sem_asgn_var).
  + apply H0.(asgn_sem_other_var).
  + rewrite H.
    apply H0.(asgn_sem_asgn_var).
  + apply H0.(asgn_sem_other_var).
Qed.

#[export] Instance seq_sem_congr:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) seq_sem.
Proof. apply Rels_concat_congr. Qed.

#[export] Instance test_true_congr:
  Proper (func_equiv _ _ ==> Sets.equiv) test_true.
Proof.
  unfold Proper, respectful, test_true.
  unfold func_equiv, pointwise_relation; sets_unfold;
  intros D1 D2 H s1 s2.
  rewrite H.
  tauto.
Qed.

#[export] Instance test_false_congr:
  Proper (func_equiv _ _ ==> Sets.equiv) test_false.
Proof.
  unfold Proper, respectful, test_false.
  unfold func_equiv, pointwise_relation; sets_unfold;
  intros D1 D2 H s1 s2.
  rewrite H.
  tauto.
Qed.

#[export] Instance if_sem_congr:
  Proper (func_equiv _ _ ==>
          Sets.equiv ==>
          Sets.equiv ==>
          Sets.equiv) if_sem.
Proof.
  unfold Proper, respectful, if_sem.
  intros D01 D02 H0 D11 D12 H1 D21 D22 H2.
  rewrite H0, H1, H2.
  reflexivity.
Qed.

#[export] Instance while_sem_congr:
  Proper (func_equiv _ _ ==>
          Sets.equiv ==>
          Sets.equiv) while_sem.
Proof.
  unfold Proper, respectful, while_sem.
  intros D01 D02 H0 D11 D12 H1.
  apply Sets_indexed_union_congr.
  intros n.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn, H0, H1.
    reflexivity.
Qed.

(** 下面证明Simplewhile程序语句行为等价的代数性质。*)

#[export] Instance cequiv_equiv: Equivalence cequiv.
Proof.
  unfold cequiv.
  apply equiv_in_domain.
  apply Sets_equiv_equiv.
Qed.

#[export] Instance CAsgn_congr:
  Proper (eq ==> iequiv ==> cequiv) CAsgn.
Proof.
  unfold Proper, respectful, cequiv, iequiv.
  intros; simpl.
  apply asgn_sem_congr; tauto.
Qed.

#[export] Instance CSeq_congr:
  Proper (cequiv ==> cequiv ==> cequiv) CSeq.
Proof.
  unfold Proper, respectful, cequiv.
  intros; simpl.
  apply seq_sem_congr; tauto.
Qed.

#[export] Instance CIf_congr:
  Proper (bequiv ==> cequiv ==> cequiv ==> cequiv) CIf.
Proof.
  unfold Proper, respectful, bequiv, cequiv; intros.
  intros; simpl.
  apply if_sem_congr; tauto.
Qed.

#[export] Instance CWhile_congr:
  Proper (bequiv ==> cequiv ==> cequiv) CWhile.
Proof.
  unfold Proper, respectful, bequiv, cequiv; intros.
  intros; simpl.
  apply while_sem_congr; tauto.
Qed.

(** 更多关于程序行为的有用性质可以使用集合与关系的运算性质完成证明，_[seq_skip]_与
    _[skip_seq]_表明了删除顺序执行中多余的空语句不改变程序行为。*)

Lemma seq_skip:
  forall c, [[ c; skip ]] ~=~ c.
Proof.
  intros.
  unfold cequiv.
  unfold_sem.
  apply Rels_concat_id_r.
Qed.

Lemma skip_seq:
  forall c, [[ skip; c ]] ~=~ c.
Proof.
  intros.
  unfold cequiv.
  unfold_sem.
  apply Rels_concat_id_l.
Qed.

(** 类似的，_[seq_assoc]_表明顺序执行的结合顺序是不影响程序行为的，因此，所有实际的编
    程中都不需要在程序开发的过程中额外标明顺序执行的结合方式。*)

Lemma seq_assoc: forall c1 c2 c3,
  [[ (c1; c2); c3 ]] ~=~ [[ c1; (c2; c3) ]].
Proof.
  intros.
  unfold cequiv.
  unfold_sem.
  apply Rels_concat_assoc.
Qed.

(** 前面提到，while循环语句的行为也可以描述为：只要循环条件成立，就先执行循环体再重新执
    行循环。我们可以证明，我们目前定义的程序语义符合这一性质。*)

Lemma while_unroll1: forall e c,
  [[ while (e) do {c} ]] ~=~
  [[ if (e) then { c; while (e) do {c} } else {skip} ]].
Proof.
  unfold cequiv.
  intros; simpl.
  unfold while_sem, if_sem, seq_sem, skip_sem.
  rewrite Rels_concat_id_r.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_indexed_union_included.
    intros n.
    destruct n; simpl.
    - apply Sets_empty_included.
    - rewrite <- (Sets_included_indexed_union n).
      reflexivity.
  + apply Sets_union_included.
    - rewrite Rels_concat_indexed_union_distr_l.
      rewrite Rels_concat_indexed_union_distr_l.
      apply Sets_indexed_union_included; intros.
      rewrite <- (Sets_included_indexed_union (S n)).
      simpl.
      apply Sets_included_union1.
    - rewrite <- (Sets_included_indexed_union (S O)).
      simpl boundedLB.
      apply Sets_included_union2.
Qed.

(** 最后，我们再证明一个while循环语句的例子。*)

#[export] Instance ceval_congr:
  Proper (cequiv ==> Sets.equiv) eval_com.
Proof.
  unfold Proper, respectful, cequiv.
  tauto.
Qed.

Example loop_to_5_fact:
  forall s1 s2,
    (s1, s2) ∈ ⟦ while ("x" < 5) do { "x" = "x" + 1 } ⟧ ->
    s1 "x" = 1 ->
    s2 "x" = 5.
Proof.
  intros.
  rewrite while_unroll1 in H.
  choose_if_then_branch H.
  destruct_concat H as [s1' H1 H].
  pose proof H1.(asgn_sem_asgn_var).
  unfold_sem in H2.
  rewrite H0 in H2.
  clear s1 H1 H0.
  rename s1' into s1, H2 into H0.

  rewrite while_unroll1 in H.
  choose_if_then_branch H.
  destruct_concat H as [s1' H1 H].
  pose proof H1.(asgn_sem_asgn_var).
  unfold_sem in H2.
  rewrite H0 in H2.
  clear s1 H1 H0.
  rename s1' into s1, H2 into H0.

  rewrite while_unroll1 in H.
  choose_if_then_branch H.
  destruct_concat H as [s1' H1 H].
  pose proof H1.(asgn_sem_asgn_var).
  unfold_sem in H2.
  rewrite H0 in H2.
  clear s1 H1 H0.
  rename s1' into s1, H2 into H0.

  rewrite while_unroll1 in H.
  choose_if_then_branch H.
  destruct_concat H as [s1' H1 H].
  pose proof H1.(asgn_sem_asgn_var).
  unfold_sem in H2.
  rewrite H0 in H2.
  clear s1 H1 H0.
  rename s1' into s1, H2 into H0.

  rewrite while_unroll1 in H.
  choose_if_else_branch H.
  unfold_sem in H.
  sets_unfold in H.
  subst s2.
  lia.
Qed.



End DntSem_SimpleWhile3_Properties.

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope list.
Local Open Scope Z.

(** * Coq标准库中的list *)

Module ListDemo.

(** 在Coq中，_[list X]_表示一列_[X]_类型的元素，在标准库中，这一类型是通过Coq归
    纳类型定义的。下面介绍它的定义方式，重要函数与性质。此处为了演示这些函数的定
    义方式以及从定义出发构建各个性质的具体步骤重新按照标准库定义了_[list]_，下面
    的所有定义和性质都可以从标准库中找到。*)

Inductive list (X: Type): Type :=
  | nil: list X
  | cons (x: X) (l: list X): list X.

(** 这里，_[nil]_表示，这是一个空列；_[cons]_表示一个非空列由一个元素（头元素）
    和另外一列元素（其余元素）构成，因此_[list]_可以看做用归纳类型表示的树结构的
    退化情况。下面是两个整数列表_[list Z]_的例子。*)

Check (cons Z 3 (nil Z)).
Check (cons Z 2 (cons Z 1 (nil Z))).

(** Coq中也可以定义整数列表的列表，_[list (list Z)]_。*)

Check (cons (list Z) (cons Z 2 (cons Z 1 (nil Z))) (nil (list Z))).

(** 我们可以利用Coq的隐参数机制与_[Arguments]_指令，让我们省略_[list]_定义中的类
    型参数。*)

Arguments nil {X}.
Arguments cons {X} _ _.

(** 例如，我们可以重写上面这些例子: *)

Check (cons 3 nil).
Check (cons 2 (cons 1 nil)).
Check (cons (cons 2 (cons 1 nil)) nil).

(** Coq标准库还提供了一些_[Notation]_让_[list]_相关的描述变得更简单。目前，读者不需要
    了解或掌握相关声明的语法规定。*)

Notation "x :: y" := (cons x y)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

(** 下面用同一个整数列表的三种表示方法来演示这些_[Notation]_的使用方法。*)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1; 2; 3].

(** 总的来说，我们在Coq中利用归纳类型_[list]_定义了我们日常理解的“列表”。这种定义方式
    从理论角度看是完备的，换言之，每一个_[A]_类型对象构成的（有穷长）列表都有一个
    _[list A]_类型的元素与之对应，反之亦然。但是，许多我们直观看来“列表”显然应当具备的
    性质，在Coq中都不是显然成立的，它们需要我们在Coq中利用归纳类型相关的方式做出证明；
    同时，所有“列表”相关的变换、函数与谓词，无论其表达的意思多么简单，它们都需要我们在
    Coq中利用归纳类型相关的方式做出定义。

    下面介绍一些关于_[list]_的常用函数。根据Coq的要求，归纳类型上的递归函数必须依据归
    纳定义的方式进行递归。换言之，要定义_[list]_类型上的递归函数，就要能够计算这个
    _[list]_取值为_[nil]_的结果，并将这个_[list]_取值为_[cons a l]_时的结果规约为取
    值为_[l]_时的结果。很多关于列表的直观概念，都需要通过这样的方式导出，例如列表的长
    度、列表第i项的值、两个列表的连接等等。 

    下面定义的函数_[app]_表示列表的连接。*)

Fixpoint app {A: Type} (l1 l2: list A): list A :=
  match l1 with
  | nil        => l2
  | cons a l1' => cons a (app l1' l2)
  end.

(** 在Coq中一般可以用_[++]_表示_[app]_，这个符号的结合性被规定为右结合。 *)

Notation "x ++ y" := (app x y)
  (right associativity, at level 60).

(** 以我们的日常理解看，“列表连接”的含义是不言自明的，就是把两个列表“连起来”。例如：
   
        [1; 2; 3] ++ [4; 5] = [1; 2; 3; 4; 5]
        [0; 0] ++ [0; 0; 0] = [0; 0; 0; 0; 0]
      
    在Coq标准库定义_[app]_时，_[[1; 2; 3]]_与后续列表的连接被规约为_[[2; 3]]_与后续
    列表的连接，又进一步规约为_[[3]]_与后续列表的连接，以此类推。
   
        [1; 2; 3] ++ [4; 5] =
        1 :: ([2; 3] ++ [4; 5]) =
        1 :: (2 :: ([3] ++ [4; 5])) =
        1 :: (2 :: (3 :: ([] ++ [4; 5]))) =
        1 :: (2 :: (3 :: [4; 5])) = 
        [1; 2; 3; 4; 5]
      

    我们可以在Coq中写下一些例子，检验上面定义的_[app]_（也是Coq标准库中的_[app]_）确
    实定义了列表的连接。*)

Example test_app1: [1; 2; 3] ++ [4; 5] = [1; 2; 3; 4; 5].
Proof. reflexivity.  Qed.
Example test_app2: [2] ++ [3] ++ [] ++ [4; 5] = [2; 3; 4; 5].
Proof. reflexivity.  Qed.
Example test_app3: [1; 2; 3] ++ nil = [1; 2; 3].
Proof. reflexivity.  Qed.

(** 上面定义_[app]_时我们只能使用Coq递归函数，下面要证明关于它的性质，我们也只能从Coq
    中的依据定义证明、结构归纳法证明与分类讨论证明开始。等证明了一些关于它的基础性质
    后，才可以使用这些性质证明进一步的结论。

    我们熟知，空列表与任何列表连接，无论空列表在左还是空列表在右，都会得到这个列表本
    身。这可以在Coq中写作下面两个定理。*)

Theorem app_nil_l: forall A (l: list A), [] ++ l = l.
Proof. intros. simpl. reflexivity. Qed.

Theorem app_nil_r: forall A (l: list A), l ++ [] = l.
Proof.
  intros.
  induction l as [| n l' IHl'].
  + reflexivity.
  + simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

(** 其中，_[app_nil_l]_的证明只需使用_[app]_的定义化简_[[] ++ l]_即可。而
    _[app_nil_r]_的证明需要对列表作结构归纳。不过，这一归纳证明的思路是很简单的，以

        _[[1; 2; 3] ++ []]_ 

    的情况为例，归纳步骤的证明如下：
   
        [1; 2; 3] ++ [] =
        (1 :: [2; 3]) ++ [] =
        1 :: ([2; 3] ++ []) =
        1 :: ([2; 3]) =
        [1; 2; 3]
      
    其中第3行到第4行所做变换就是归纳假设。

    我们还熟知，列表的连接具有结合律，在Coq中这一性质可以写作如下定理。*)

Theorem app_assoc:
  forall A (l1 l2 l3: list A),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.

(** 若要证明这一定理，无非是选择对_[l1]_做归纳、对_[l2]_做归纳还是对_[l3]_做归纳证
    明。无论选择哪一种，结构归纳证明中的奠基步骤都没有问题，只需使用前面证明的
    _[app_nil_l]_与_[app_nil_r]_即可：
   
        [] ++ (l2 ++ l3) = l2 ++ l3 = ([] ++ l2) ++ l3
        l1 ++ ([] ++ l3) = l1 ++ l3 = (l1 ++ []) ++ l3
        l1 ++ (l2 ++ []) = l1 ++ l2 = (l1 ++ l2) ++ []
      
    然而，三种归纳证明的选择中，只有对_[l1]_归纳我们才能顺利地完成归纳步骤的证明。因为
    _[app]_的定义是对左侧列表做结构递归定义的，所以我们不难写出下面变换：
   
        (a :: l1) ++ (l2 ++ l3) =
        a :: (l1 ++ (l2 ++ l3)) 
   
        ((a :: l1) ++ l2) ++ l3) =
        (a :: (l1 ++ l2)) ++ l3) =
        a :: ((l1 ++ l2) ++ l3))
      
    这样一来，我们就可以利用归纳假设完成归纳步骤的证明了。相反，如果采取对_[l2]_归纳证
    明或对_[l3]_归纳证明的策略，那么我们对于形如：

        _[(l1 ++ (a :: l2)) ++ l3]_ 

        _[(l1 ++ l2) ++ (a :: l3)]_ 

    就束手无策了！尽管我们知道_[l1 ++ (a :: l2) = (l1 ++ [a]) ++ l2]_，但是我们没有
    在Coq中证明过这一性质，因而也就无法在此使用这样的性质做证明。

    我们把上面总结的“对_[l1]_做结构归纳证明”的策略写成Coq证明如下。*)
Proof.
  intros.
  induction l1; simpl.
  + reflexivity.
  + rewrite -> IHl1.
    reflexivity.
Qed.

(** 下面这条性质与前面所证明的性质有所不同，它从两个列表连接的结果反推两个列表。这条
    Coq定理说的是：如果_[l1 ++ l2]_是空列表，那么_[l1]_与_[l2]_都是空列表。*)

Theorem app_eq_nil:
  forall A (l1 l2: list A),
    l1 ++ l2 = [] ->
    l1 = [] /\ l2 = [].

(** 要证明这一条性质，比较常见的思路是先利用反证法证明_[l1 = []]_，再利用这一结论证明
    _[l2 = []]_。具体而言，在利用反证法证明_[l1 = []]_时，我们先假设 

        _[l1 = a :: l1']_ 

    由此不难推出：

        _[l1 ++ l2 = (a :: l1') ++ l2 = a :: (l1' ++ l2)]_ 

    这与_[l1 ++ l2 = []]_是矛盾的。因此，_[l1 = []]_。进一步，由_[app]_的定义又可
    知，

        _[l1 ++ l2 = [] ++ l2 = l2]_ 

    根据_[l1 ++ l2 = []]_的条件，这就意味着_[l2 = []]_。这样我们就证明了全部的结论。
    下面是上述证明思路在Coq中的表述。Coq证明中我们并没有真正采用反证法，事实上，我们使
    用了Coq中基于归纳类型的分类讨论证明。具体而言，我们在这段证明中对_[l1]_的结构做了
    分类讨论：当_[l1]_为空列表时，我们证明_[l2]_也必须是空列表；当_[l1]_为非空列表
    时，我们推出矛盾。*)

Proof.
  intros.
  destruct l1.
  + (** 当_[l1]_为空列表时，需由_[[] ++ l2 = []]_证明_[[] = [] /\ l2 = []]_。*)
    simpl in H.
    tauto.
  + (** 当_[l1]_非空时，需要推出矛盾。*)
    simpl in H.
    discriminate H.
Qed.

(** 到此为止，我们介绍了列表连接函数_[app]_的定义与其重要基础性质的证明。类似的，可以
    定义Coq递归函数_[rev]_表示对列表取反，并证明它的基础性质。*)

Fixpoint rev {A: Type} (l: list A) : list A :=
  match l with
  | nil       => nil
  | cons a l' => rev l' ++ [a]
  end.

Example test_rev1: rev [1; 2; 3] = [3; 2; 1].
Proof. reflexivity. Qed.
Example test_rev2: rev [1; 1; 1; 1] = [1; 1; 1; 1].
Proof. reflexivity. Qed.
Example test_rev3: @rev Z [] = [].
Proof. reflexivity. Qed.

(** 下面几个性质的证明留作习题。*)

(************)
(** 习题：  *)
(************)

Theorem rev_app_distr:
  forall A (l1 l2: list A),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Theorem rev_involutive:
  forall A (l: list A), rev (rev l) = l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 如果熟悉函数式编程，不难发现，上面的_[rev]_定义尽管在数学是简洁明确的，但是
    其计算效率是比较低的。相对而言，利用下面的_[rev_append]_函数进行计算则效率较
    高。*)

Fixpoint rev_append {A} (l1 l2: list A): list A :=
  match l1 with
  | []       => l2
  | a :: l1' => rev_append l1' (a :: l2)
  end.

(** 下面以_[[1; 2; 3; 4]]_的取反为例做对比。
   
        rev [1; 2; 3; 4] =
        rev [2; 3; 4] ++ [1] =
        (rev [3; 4] ++ [2]) ++ [1] =
        ((rev [4] ++ [3]) ++ [2]) ++ [1] =
        (((rev [] ++ [4]) ++ [3]) ++ [2]) ++ [1] =
        ((([] ++ [4]) ++ [3]) ++ [2]) ++ [1] =
        [4; 3; 2; 1] 
   
        rev_append [1; 2; 3; 4] [] =
        rev_append [2; 3; 4] [1] =
        rev_append [3; 4] [2; 1] =
        rev_append [4] [3; 2; 1] =
        rev_append [] [4; 3; 2; 1] =
        [4; 3; 2; 1]
      
    看上去两个函数的计算过程都包含四个递归步骤，但是_[rev]_的计算中还需要计算列表的连
    接“_[++]_”，因此它的总时间复杂度更高。下面证明_[rev]_与_[rev_append]_的计算结果
    相同，而证明的关键就是使用加强归纳法先证明下面引理。*)

Lemma rev_append_rev:
  forall A (l1 l2: list A),
    rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros.
  revert l2; induction l1 as [| a l1 IHl1]; intros; simpl.
  + reflexivity.
  + rewrite IHl1.
    rewrite <- app_assoc.
    reflexivity.
Qed.

(** 利用这一引理，就可以直接证明下面结论了。*)

Theorem rev_alt:
  forall A (l: list A), rev l = rev_append l [].
Proof.
  intros.
  rewrite rev_append_rev.
  rewrite app_nil_r.
  reflexivity.
Qed.

(** 下面再介绍一个关于列表的常用函数_[map]_，它表示对一个列表中的所有元素统一做映射。
    它是一个Coq中的高阶函数。*)

Fixpoint map {X Y: Type} (f: X -> Y) (l: list X): list Y :=
  match l with
  | nil       => nil
  | cons x l' => cons (f x) (map f l')
  end.

(** 这是一些例子： *)

Example test_map1: map (fun x => x - 2) [7; 5; 7] = [5; 3; 5].
Proof. reflexivity. Qed.
Example test_map2: map (fun x => x * x) [2; 1; 5] = [4; 1; 25].
Proof. reflexivity. Qed.
Example test_map3: map (fun x => [x]) [0; 1; 2; 3] = [[0]; [1]; [2]; [3]].
Proof. reflexivity. Qed.

(** 很自然，如果对两个函数的复合做_[map]_操作，就相当于先后对这两个函数做_[map]_操作。
    这在Coq中可以很容易地利用归纳法完成证明。*)

Theorem map_map:
  forall X Y Z (f: Y -> Z) (g: X -> Y) (l: list X),
    map f (map g l) = map (fun x => f (g x)) l.
Proof.
  intros.
  induction l; simpl.
  + reflexivity.
  + rewrite IHl.
    reflexivity.
Qed.

(** 关于_[map]_的其他重要性质的证明，我们留作习题。*)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[map]_的性质。*)

Theorem map_app:
  forall X Y (f: X -> Y) (l l': list X),
    map f (l ++ l') = map f l ++ map f l'.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[map]_的性质。*)

Theorem map_rev:
  forall X Y (f: X -> Y) (l: list X),
    map f (rev l) = rev (map f l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[map]_的性质。*)

Theorem map_ext:
  forall X Y (f g: X -> Y),
    (forall a, f a = g a) ->
    (forall l, map f l = map g l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[map]_的性质。*)

Theorem map_id:
  forall X (l: list X), map (fun x => x) l = l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 除了提供一系列关于列表的常用函数之外，Coq标准库还提供了不少关于列表的谓词。这里我们
    只介绍其中最常用的一个：_[In]_。*)

Fixpoint In {A: Type} (a: A) (l: list A): Prop :=
  match l with
  | nil => False
  | b :: l' => b = a \/ In a l'
  end.

(** 根据这一定义，_[In a l]_表示_[a]_是_[l]_的一个元素。可以证明_[In a l]_的充分必
    要条件是_[l]_可以写成_[l1 ++ a :: l2]_的形式。

    首先是充分性。要由_[l = l1 ++ a :: l2]_推出_[In a l]_可以直接写作下面更简单的形
    式。*)

Theorem in_elt:
  forall A (a: A) (l1 l2: list A),
    In a (l1 ++ a :: l2).

(** 证明时，对_[l1]_使用归纳证明上面命题，也比对_[l]_归纳证明_[l = l1 ++ a :: l2]_能
    推出_[In a l]_来得方便。下面是Coq证明。*)

Proof.
  intros.
  induction l1 as [| b l1 IHl1]; simpl.
  + tauto.
  + tauto.
Qed.

(** 在证明必要性之前，我们先证明一个引理：如果_[a]_出现在_[l]_中，那么_[a]_也出现在
    _[b::l]_中。*)

Lemma elt_cons:
  forall A (a b: A) (l: list A),
    (exists l1 l2, l = l1 ++ a :: l2) ->
    (exists l1 l2, b :: l = l1 ++ a :: l2).
Proof.
  intros A a b l [l1 [l2 H]].
  exists (b :: l1), l2.
  rewrite H.
  reflexivity.
Qed.

(** 在上面证明中，我们利用前提_[H: l = l1 ++ a :: l2]_以及_[rewrite H]_指令将结论中
    的_[l]_变为了_[l1 ++ a :: l2]_。在Coq证明中，我们经常需要利用等式将一个变量替换为
    与它相等的式子，有时可能还需要在前提和结论中替换多处。Coq提供了_[subst]_指令用于完
    成这样的变换。*)

Lemma elt_cons_again:
  forall A (a b: A) (l: list A),
    (exists l1 l2, l = l1 ++ a :: l2) ->
    (exists l1 l2, b :: l = l1 ++ a :: l2).
Proof.
  intros A a b l [l1 [l2 H]].
  exists (b :: l1), l2.
  subst l.
  (** 在执行完_[subst l]_指令后，结论中的_[l]_被替换为了_[l1 ++ a :: l2]_并且前提中
      的_[H]_以及_[l]_都被删除了。*)
  reflexivity.
Qed.

(** 下面证明必要性定理。*)

Theorem in_split:
  forall A (a: A) (l: list A),
    In a l ->
    exists l1 l2, l = l1 ++ a :: l2.
Proof.
  intros.
  induction l as [| b l IHl]; simpl in *.
  + (** 奠基步骤是_[l]_为空列表的情况，此时可以直接由_[In a l]]_推出矛盾。*)
    tauto.
  + (** 归纳步骤是要由_[In a l]_情况下的归纳假设推出_[In a (b :: l)]_时的结论。下面 
        先对_[In a (b :: l)]_这一前提成立的原因做分类讨论。*)
    destruct H.
    - (** 情况一：_[b = a]_。这一情况下结论是容易证明的，我们将使用_[subst b]_指令将
          _[b]_都替换为_[a]_。 *)
      exists nil, l.
      subst b; reflexivity.
    - (** 情况二：_[In a l]_。这一情况下可以使用归纳假设与_[elt_cons]_引理完成证明。*)
      specialize (IHl H).
      apply elt_cons, IHl.
Qed.

(** 下面再列举几条关于_[In]_的重要性质。它们的Coq证明都可以在Coq代码中找到。首先，
    _[l1 ++ l2]_的元素要么是_[l1]_的元素要么是_[l2]_的元素；_[rev l]_的元素全都是
    _[l]_的元素。*)

Theorem in_app_iff:
  forall A (l1 l2: list A) (a: A),
    In a (l1 ++ l2) <-> In a l1 \/ In a l2.
Proof.
  intros.
  induction l1 as [| b l1 IHl1]; simpl.
  + tauto.
  + rewrite IHl1.
    tauto.
Qed.

Theorem in_rev:
  forall A (l: list A) (a: A),
    In a l <-> In a (rev l).
Proof.
  intros.
  induction l as [| b l IHl]; simpl.
  + tauto.
  + rewrite in_app_iff.
    simpl.
    tauto.
Qed.

(** 接下去两条定理探讨了_[map f l]_中元素具备的性质，其中_[in_map]_给出了形式较为简洁
    的必要条件，而_[in_map_iff]_给出的充要条件其形式要复杂一些。*)

Theorem in_map:
  forall A B (f: A -> B) (l: list A) (a: A),
    In a l -> In (f a) (map f l).
Proof.
  intros.
  induction l as [| a0 l IHl]; simpl in *.
  + tauto.
  + destruct H.
    - subst a0.
      tauto.
    - tauto.
Qed.

Theorem in_map_iff:
  forall A B (f: A -> B) (l: list A) (b: B),
    In b (map f l) <->
    (exists a, f a = b /\ In a l).
Proof.
  intros.
  induction l as [| a0 l IHl]; simpl.
  + split.
    - tauto.
    - intros [a ?].
      tauto.
  + rewrite IHl.
    split.
    - intros [? | [a [? ?]]].
      * exists a0.
        tauto.
      * exists a.
        tauto.
    - intros [a [? [? | ?]]].
      * subst a.
        tauto.
      * right; exists a.
        tauto.
Qed.

(** 以上介绍的列表相关定义域性质都可以在Coq标准库中找到。使用时，只需要导入
    _[Coq.Lists.List]_即可。*)

End ListDemo.

(************)
(** 习题：  *)
(************)

(** 下面定义的_[suffixes]_函数计算了一个列表的所有后缀。*)

Fixpoint suffixes {A: Type} (l: list A): list (list A) :=
  match l with
  | nil => [nil]
  | a :: l' => l :: suffixes l'
  end.

(** 例如 
   
        suffixes []           = [ [] ]
        suffixes [1]          = [ [1]; [] ]
        suffixes [1; 2]       = [ [1; 2]; [2]; [] ]
        suffixes [1; 2; 3; 4] = [ [1; 2; 3; 4];
                                  [2; 3; 4]   ;
                                  [3; 4]      ;
                                  [4]         ;
                                  []          ]
      
    接下去，请分三步证明，_[suffixes l]_中的确实是_[l]_的全部后缀。*)

Lemma self_in_suffixes:
  forall A (l: list A), In l (suffixes l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem in_suffixes:
  forall A (l1 l2: list A),
    In l2 (suffixes (l1 ++ l2)).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem in_suffixes_inv:
  forall A (l2 l: list A),
    In l2 (suffixes l) ->
    exists l1, l1 ++ l2 = l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 下面定义的_[prefixes]_函数计算了一个列表的所有前缀。*)

Fixpoint prefixes {A: Type} (l: list A): list (list A) :=
  match l with
  | nil => [nil]
  | a :: l0 => nil :: (map (cons a) (prefixes l0))
  end.

(** 例如：
   
        prefixes [1; 2]    = [ []     ;
                               [1]    ;
                               [1; 2] ] 
   
        prefixes [0; 1; 2] = [] ::
                             map (cons 0 (prefixes [1; 2]))
                           = [] ::
                             [ 0 :: []     ;
                               0 :: [1]    ;
                               0 :: [1; 2] ]
                           = [ []        ;
                               [0]       ;
                               [0; 1]    ;
                               [0; 1; 2] ]
      
    接下去，请分三步证明，_[prefixes l]_中的确实是_[l]_的全部前缀。*)

Lemma nil_in_prefixes:
  forall A (l: list A), In nil (prefixes l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem in_prefixes:
  forall A (l1 l2: list A),
    In l1 (prefixes (l1 ++ l2)).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem in_prefixes_inv:
  forall A (l1 l: list A),
    In l1 (prefixes l) ->
    exists l2, l1 ++ l2 = l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 下面的_[sublists]_定义了列表中的所有连续段。*)

Fixpoint sublists {A: Type} (l: list A): list (list A) :=
  match l with
  | nil => [nil]
  | a :: l0 => map (cons a) (prefixes l0) ++ sublists l0
  end.

(** 请证明_[sublists l]_的元素确实是_[l]_中的所有连续段。提示：必要时可以添加并证明一
    些前置引理帮助完成证明。*)

Theorem in_sublists:
  forall A (l1 l2 l3: list A),
    In l2 (sublists (l1 ++ l2 ++ l3)).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem in_sublists_inv:
  forall A (l2 l: list A),
    In l2 (sublists l) ->
    exists l1 l3, l1 ++ l2 ++ l3 = l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** * 列表相关的证明技巧 *)

(** 在基于_[list]_的计算中，有两类常见的计算，一类是从左向右计算，一类是从右向左计算。
    以对整数序列求和为例，下面的_[sum_L2R]_刻画了从左向右的计算方法，而_[sum_R2L]_刻
    画了从右向左的计算方法。*)

Fixpoint sum_L2R_rec (l: list Z) (s: Z): Z :=
  match l with
  | nil       => s
  | cons z l' => sum_L2R_rec l' (s + z)
  end.

Definition sum_L2R (l: list Z): Z := sum_L2R_rec l 0.

Fixpoint sum_R2L (l: list Z): Z :=
  match l with
  | nil       => 0
  | cons z l' => z + sum_R2L l'
  end.

(** 以对_[[1; 3; 5; 7]]_求和为例。 
   
        sum_L2R [1; 3; 5; 7] =
        sum_L2R_rec [1; 3; 5; 7] 0 =
        sum_L2R_rec [3; 5; 7] (0 + 1) =
        sum_L2R_rec [5; 7] ((0 + 1) + 3) =
        sum_L2R_rec [7] (((0 + 1) + 3) + 5) =
        sum_L2R_rec [] ((((0 + 1) + 3) + 5) + 7) =
        (((0 + 1) + 3) + 5) + 7 

   
        sum_R2L [1; 3; 5; 7] =
        1 + sum_R2L [3; 5; 7] = 
        1 + (3 + sum_R2L [5; 7]) =
        1 + (3 + (5 + sum_R2L [7])) =
        1 + (3 + (5 + (7 + sum_R2L []))) =
        1 + (3 + (5 + (7 + 0))) 

    许多列表上的运算都可以归结为从左向右计算和从右向左计算。Coq标准库把这样的通用计算模
    式刻画为_[fold_left]_与_[fold_right]_。

   
      Fixpoint fold_left {A B: Type} (f: A -> B -> A) (l: list B) (a0: A): A :=
        match l with
        | nil       => a0
        | cons b l' => fold_left f l' (f a0 b)
        end.
      

   
      Fixpoint fold_right {A B: Type} (f: A -> B -> B) (b0: B) (l: list A): B :=
        match l with
        | nil       => b0
        | cons a l' => f a (fold_right f b0 l')
        end.
      

    仔细观察，不难发现_[sum_L2R]_与_[sum_R2L]_可以分别用_[fold_left]_与
    _[fold_right]_表示出来。下面是它们的对应关系。*)

Fact sum_L2R_rec_is_fold_left:
  forall (l: list Z) (s: Z),
    sum_L2R_rec l s = fold_left (fun z1 z2 => z1 + z2) l s.
Proof.
  intros.
  revert s; induction l; intros; simpl.
  + reflexivity.
  + apply IHl.
Qed.

Fact sum_L2R_is_fold_left:
  forall l: list Z,
    sum_L2R l = fold_left (fun z1 z2 => z1 + z2) l 0.
Proof.
  intros.
  unfold sum_L2R.
  apply sum_L2R_rec_is_fold_left.
Qed.

Fact sum_R2L_is_fold_right:
  forall l: list Z,
    sum_R2L l = fold_right (fun z1 z2 => z1 + z2) 0 l.
Proof.
  intros.
  induction l; simpl.
  + reflexivity.
  + rewrite IHl.
    reflexivity.
Qed.

(** 当然，我们都知道，根据加法结合律_[sum_L2R]_与_[sum_R2L]_应当相等。不过，我们无法
    直接证明这一结论。直接使用归纳法证明很快就会陷入困境。*)

Theorem sum_L2R_sum_R2L:
  forall (l: list Z),
    sum_L2R l = sum_R2L l.
Proof.
  intros.
  induction l.
  + (** 由于_[sum_L2R [] = sum_L2R_rec [] 0 = 0]_并且_[sum_R2L [] = 0]_，所以奠
        基步骤的结论显然成立。*)
    reflexivity.
  + (** 根据定义
        - sum_R2L (a :: l) = a + sum_R2L l
        - sum_L2R (a :: l) = sum_L2R_rec (a :: l) 0 = sum_L2R_rec l a
        于是后者无法被归结为关于_[sum_L2R l]_或者_[sum_L2R_rec l 0]_的式子，自然也
        就无法使用归纳假设证明_[sum_L2R (a :: l)]_与_[sum_R2L (a :: l)]_相等。*)
Abort.

(** 一些读者会想到先证明一个形如_[sum_L2R_rec l a = a + sum_L2R l]_的引理从而完成上
    面的归纳证明。这是可行的，其中关键的归纳步骤是要证明，如果下面归纳假设成立 

        _[forall s, sum_L2R_rec l s = s + sum_L2R_rec l 0]_ 

    那么 

        _[sum_L2R_rec (a :: l) s = s + sum_L2R_rec (a :: l) 0]_。 

    根据定义和归纳假设我们知道：
   
        sum_L2R_rec (a :: l) s =
        sum_L2R_rec l (s + a) =
        (s + a) + sum_L2R_rec l 0 
   
        s + sum_L2R_rec (a :: l) 0 =
        s + sum_L2R_rec l a =
        s + (a + sum_L2R_rec l 0)
      
    这样就能完成归纳步骤的证明了。上述证明的Coq版本如下。*)

Lemma sum_L2R_rec_sum_L2R:
  forall (s: Z) (l: list Z),
    sum_L2R_rec l s = s + sum_L2R l.
Proof.
  intros.
  unfold sum_L2R.
  revert s; induction l; simpl; intros.
  + lia.
  + rewrite (IHl a), (IHl (s + a)).
    lia.
Qed.

(** 基于此证明原先的定理_[sum_L2R_sum_R2L]_是容易的。 *)

Theorem sum_L2R_sum_R2L:
  forall (l: list Z), sum_L2R l = sum_R2L l.
Proof.
  intros.
  induction l.
  + reflexivity.
  + unfold sum_L2R; simpl.
    rewrite sum_L2R_rec_sum_L2R.
    lia.
Qed.

(** 上面的证明思路是从结论出发，尝试是否可以通过对_[l]_归纳证明
    _[sum_L2R l = sum_R2L l]_，并在证明中根据需要补充证明相关的引理。同样是要证明这一
    结论，还有下面这一种不同的证明方案，它的主要思路是从_[sum_L2R]_和_[sum_R2L]_两者
    定义的结构出发构造证明。在这两者的定义中，_[sum_R2L]_和_[sum_L2R_rec]_都是对列表
    递归定义的函数，因此可以优先证明此二者之间的联系。*)

Lemma sum_L2R_rec_sum_R2L:
  forall (s: Z) (l: list Z),
    sum_L2R_rec l s = s + sum_R2L l.
Proof.
  intros.
  revert s; induction l; intros; simpl.
  + lia.
  + rewrite IHl.
    lia.
Qed.

(** 在此基础上就可以导出_[sum_L2R]_和_[sum_R2L]_等价。*)

Theorem sum_L2R_sum_R2L_____second_proof:
  forall (l: list Z), sum_L2R l = sum_R2L l.
Proof.
  intros.
  unfold sum_L2R.
  rewrite sum_L2R_rec_sum_R2L.
  lia.
Qed.

(** 回顾_[sum_L2R]_与_[sum_R2L]_的定义，其实称它们分别是从左向右计算和从右向左有两方
    面的因素。第一是从结果看：

         _[sum_L2R [1; 3; 5; 7] = (((0 + 1) + 3) + 5) + 7]_ 

         _[sum_R2L [1; 3; 5; 7] = 1 + (3 + (5 + (7 + 0)))]_ 

    第二是从计算过程看，
   
        sum_L2R [1; 3; 5; 7] =
        sum_L2R_rec [1; 3; 5; 7] 0 =
        sum_L2R_rec [3; 5; 7] (0 + 1) =
        sum_L2R_rec [5; 7] ((0 + 1) + 3) =
        sum_L2R_rec [7] (((0 + 1) + 3) + 5) =
        sum_L2R_rec [] ((((0 + 1) + 3) + 5) + 7) =
        (((0 + 1) + 3) + 5) + 7 
    上面_[sum_L2R]_的计算过程中，就从左向右依次计算了_[0]_、_[0 + 1]_、
    _[(0 + 1) + 3]_等等这些中间结果，而_[sum_R2L]_的计算过程就是从右向左的。这一对比
    也可以从_[sum_L2R]_与_[sum_R2L]_的定义看出。在_[sum_L2R_rec]_的递归定义中，加法
    运算出现在递归调用的参数中，也就是说，需要先计算加法运算的结果，再递归调用。由于Coq
    中_[list]_的定义是从左向右的归纳定义类型，因此，递归调用前进行计算就意味着计算过程
    是从左向右的。而_[sum_R2L]_的定义恰恰相反，它是将递归调用的结果与其他数值相加得到
    返回值，也就是说，需要先递归调用再做加法运算，因此，它的计算过程是从右向左的。 

    必须指出，从计算结果看和从计算过程看，是两种不同的视角。例如，我们还可以定义下面Coq
    函数用于表示整数列表的求和。*)

Fixpoint sum_R2L_by_L2R_rec (l: list Z) (cont: Z -> Z): Z :=
  match l with
  | nil     => cont 0
  | z :: l0 => sum_R2L_by_L2R_rec l0 (fun z0 => cont (z + z0))
  end.

Definition sum_R2L_by_L2R (l: list Z): Z :=
  sum_R2L_by_L2R_rec l (fun z => z).

(** 它从计算过程看是从左向右计算，但是它从结果看是从右向左计算，例如：
   
        sum_R2L_by_L2R [1; 3; 5; 7] =
        sum_R2L_by_L2R_rec [1; 3; 5; 7] (fun z => z) =
        sum_R2L_by_L2R_rec [3; 5; 7] (fun z => 1 + z) =
        sum_R2L_by_L2R_rec [5; 7] (fun z => 1 + (3 + z)) =
        sum_R2L_by_L2R_rec [7] (fun z => 1 + (3 + (5 + z))) =
        sum_R2L_by_L2R_rec [] (fun z => 1 + (3 + (5 + (7 + z)))) =
        1 + (3 + (5 + (7 + 0))) 
    它的计算过程中依次计算得到了 
   
        (fun z => z)
        (fun z => 1 + z)
        (fun z => 1 + (3 + z))
        (fun z => 1 + (3 + (5 + z)))
        (fun z => 1 + (3 + (5 + (7 + z))))
      
    上面这些从左到右的中间结果，但是它的最终计算结果却是从右向左的。

    我们也可以证明这个定义与先前定义的_[sum_L2R]_与_[sum_R2L]_之间的关系。我们先归纳
    证明_[sum_R2L_by_L2R_rec]_与_[sum_R2L]_之间的关系，以及_[sum_R2L_by_L2R_rec]_
    与_[sum_L2R_rec]_之间的关系，再由这两者推导出_[sum_R2L_by_L2R]_与_[sum_L2R]_、
    _[sum_R2L]_之间相等。具体的Coq证明这里略去了，这里只列出结论。*)

Lemma sum_R2L_results_aux:
  forall (cont: Z -> Z) (l: list Z),
    cont (sum_R2L l) = sum_R2L_by_L2R_rec l cont.
Proof.
  intros.
  revert cont; induction l; simpl; intros.
  + reflexivity.
  + rewrite <- IHl.
    reflexivity.
Qed.

Lemma sum_L2R_approaches_aux:
  forall (cont: Z -> Z) (s: Z) (l: list Z),
    (forall z, cont z = s + z) ->
    sum_L2R_rec l s = sum_R2L_by_L2R_rec l cont.
Proof.
  intros.
  revert s cont H; induction l; simpl; intros.
  + rewrite H.
    lia.
  + apply IHl.
    intros.
    rewrite H.
    lia.
Qed.

Theorem sum_R2L_results:
  forall l, sum_R2L l = sum_R2L_by_L2R l.
Proof.
  intros.
  unfold sum_R2L_by_L2R.
  rewrite <- sum_R2L_results_aux.
  reflexivity.
Qed.

Theorem sum_L2R_approaches:
  forall l, sum_L2R l = sum_R2L_by_L2R l.
Proof.
  intros.
  unfold sum_R2L_by_L2R, sum_L2R.
  apply sum_L2R_approaches_aux.
  lia.
Qed.

(** 一般而言，要证明两项“从左向右”计算之间的关系比较容易，要证明两种“从右向左”计算之间
    的关系也比较容易。但是要证明“从左向右”与“从右向左”之间的关系往往就要复杂一些。像上
    面分析的那样，从结论出发，采用加强归纳法证明，或者从定义出发证明辅助递归定义之间的
    关系都是常见的证明思路。

    回顾前面介绍的_[rev]_函数与_[rev_append]_函数，我们不难发现，其实_[rev]_是“从右
    向左”计算而_[rev_append]_是“从左向右”计算，而当我们证明它们计算结果相等的时候（
    _[rev_alt]_定理）也采用了类似的加强归纳法。以这样的观点来看，_[map]_函数与_[rev]_
    一样，是一个“从右向左”计算的函数。我们可以定义它的“从左向右”版本。*)

Fixpoint map_L2R_rec
           {X Y: Type}
           (f: X -> Y)
           (l: list X)
           (l': list Y): list Y :=
  match l with
  | nil        => l'
  | cons x0 l0 => map_L2R_rec f l0 (l' ++ [f x0])
  end.

Definition map_L2R {X Y: Type} (f: X -> Y) (l: list X): list Y :=
  map_L2R_rec f l [].

(************)
(** 习题：  *)
(************)

(** 请分两步证明_[map_L2R]_与_[map]_的计算结果是相等的。 *)

Lemma map_L2R_rec_map: forall X Y (f: X -> Y) l l',
  map_L2R_rec f l l' = l' ++ map f l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem map_alt: forall X Y (f: X -> Y) l,
  map_L2R f l = map f l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请试着证明下面结论。第一小题将_[fold_left]_转化为_[fold_right]_。*)

Theorem fold_left_fold_right:
  forall {A B: Type} (f: A -> B -> A) (l: list B) (a0: A),
    fold_left f l a0 =
    fold_right (fun (b: B) (g: A -> A) (a: A) => g (f a b)) (fun a => a) l a0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 第二小题是将_[fold_right]_转化为_[fold_left]_。提示：尽管这一小题看上去与第一小
    题是对称的，但是它证明起来要复杂很多，可能需要引入一条辅助引理才能完成证明。*)
Theorem fold_right_fold_left:
  forall {A B: Type} (f: A -> B -> B) (b0: B) (l: list A),
    fold_right f b0 l =
    fold_left (fun (g: B -> B) (a: A) (b: B) => g (f a b)) l (fun b => b) b0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 下面定义的_[list_inc]_定义了“整数列表单调递增”这个性质。这个定义分为两步。*)

Fixpoint list_inc_rec (a: Z) (l: list Z): Prop :=
  match l with
  | nil => True
  | cons b l0 => a < b /\ list_inc_rec b l0
  end.

Definition list_inc (l: list Z): Prop :=
  match l with
  | nil => True
  | cons a l0 => list_inc_rec a l0
  end.

(** 例如：
   
        list_inc [] = True 
   
        list_inc [x1] = list_inc_rec x1 []
                      = True 
   
        list_inc [x1; x2] = list_inc_rec x1 [x2]
                          = x1 < x2 /\ list_inc_rec x2 []
                          = x1 < x2 /\ True 
   
        list_inc [x1; x2; x3] = list_inc_rec x1 [x2; x3]
                              = x1 < x2 /\ list_inc_rec x2 [x3]
                              = x1 < x2 /\ x2 < x3 /\ list_inc_rec x3 []
                              = x1 < x2 /\ x2 < x3 /\ True
      
    下面请分两步证明，如果_[l1 ++ a1 :: a2 :: l2]_是单调递增的，那么必定有
    _[a1 < a2]_。*)

Lemma list_inc_rec_always_increasing':
  forall a l1 a1 a2 l2,
    list_inc_rec a (l1 ++ a1 :: a2 :: l2) ->
    a1 < a2.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma list_inc_always_increasing':
  forall l1 a1 a2 l2,
    list_inc (l1 ++ a1 :: a2 :: l2) ->
    a1 < a2.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 除了_[list_inc]_之外，我们也可以采取下面这种方式定义“单调递增”。*)

Definition always_increasing (l: list Z): Prop :=
  forall l1 a1 a2 l2,
    l1 ++ a1 :: a2 :: l2 = l ->
    a1 < a2.

(** 既然两种定义都表达了“单调递增”的意思，那么我们理应能够证明它们等价。先前的两个引理
    意味着我们已经可以使用_[list_inc]_推出_[always_increasing]_。这是它的Coq证明。*)

Theorem list_inc_always_increasing:
  forall l, list_inc l -> always_increasing l.
Proof.
  unfold always_increasing.
  intros.
  subst l.
  pose proof list_inc_always_increasing' _ _ _ _ H.
  tauto.
Qed.

(** 下面请你证明，_[always_increasing]_也能推出_[list_inc]_。提示：如果需要，你可以
    写出并证明一些前置引理用于辅助证明。*)

Theorem always_increasing_list_inc:
  forall l,
    always_increasing l -> list_inc l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 下面定义的_[list_sinc]_和_[strong_increasing]_都表示整数序列中的每一个元素都比它
    左侧所有元素的和还要大。值得一提的是，这里递归定义的_[list_sinc_rec]_既不是单纯的
    从左向右计算又不是单纯的从右向左计算，它的定义中既有递归调用之前的计算，又有递归调
    用之后的计算。*)

Fixpoint list_sinc_rec (a: Z) (l: list Z): Prop :=
  match l with
  | nil => True
  | cons b l0 => a < b /\ list_sinc_rec (a + b) l0
  end.

Definition list_sinc (l: list Z): Prop :=
  match l with
  | nil => True
  | cons a l0 => 0 < a /\ list_sinc_rec a l0
  end.

Definition strong_increasing (l: list Z): Prop :=
  forall l1 a l2,
    l1 ++ a :: l2 = l ->
    sum_L2R l1 < a.

(** 请你证明_[list_sinc]_与_[strong_increasing]_等价。提示：如果需要，你可以写出并证
    明一些前置引理用于辅助证明，也可以定义一些辅助概念用于证明。*)

Theorem list_sinc_strong_increasing:
  forall l, list_sinc l -> strong_increasing l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem strong_increasing_list_sinc:
  forall l,
    strong_increasing l -> list_sinc l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


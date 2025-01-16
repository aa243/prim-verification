Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
Import SetsNotation.
Local Open Scope sets_scope.
Require Import PL.StateRelMonad.
Import StateRelMonad.
Import Monad.MonadNotation.
Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.FixedPoint.
Require Import PL.Monad.
Local Open Scope monad.
Local Open Scope sets.
Import SetsNotation
       KleeneFix Sets_CPO
       Monad
       MonadNotation.
Import SetMonadHoare
       SetMonadOperator0
       SetMonadOperator1
       ListNotations
       MonadNotation.

Record PreGraph (Vertex Edge: Type) := {
  vertices : list Vertex;            (* 顶点的有限列表 *)
  edges : list Edge;                 (* 边的有限列表 *)
  src : Edge -> Vertex;              (* 边的起点 *)
  dst : Edge -> Vertex;              (* 边的终点 *)
  weight: Edge -> Z;                 (* 边的权重 *)
}.

Notation "pg '.(vertices)'" := (vertices _ _ pg) (at level 1).
Notation "pg '.(edges)'" := (edges _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).
Notation "pg '.(weight)'" := (weight _ _ pg) (at level 1).

Definition get_edges {V E: Type} (pg: PreGraph V E): list E :=
  pg.(edges).

Definition vvalid {V E: Type} (pg: PreGraph V E) : V -> Prop :=
    fun v => In v pg.(vertices).

Definition evalid {V E: Type} (pg: PreGraph V E) : E -> Prop :=
    fun e => In e pg.(edges).

Notation "pg '.(vvalid)'" := (vvalid  pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid pg) (at level 1).

Definition is_legal_graph {V E: Type} (pg: PreGraph V E): Prop :=
  forall e, pg.(evalid) e -> (pg.(vvalid) (pg.(src) e) /\ pg.(vvalid) (pg.(dst) e)).

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y \/ step_aux pg e y x.

Definition connected {V E: Type} (pg: PreGraph V E): V -> V -> Prop :=
  clos_refl_trans (step pg).

Record subgraph {V E: Type} (pg1 pg2: PreGraph V E): Prop :=
{
  subgraph_vvalid: pg1.(vvalid) ⊆ pg2.(vvalid);
  subgraph_evalid: pg1.(evalid) ⊆ pg2.(evalid);
  subgraph_src: forall e, e ∈ pg1.(evalid) -> pg1.(src) e = pg2.(src) e;
  subgraph_dst: forall e, e ∈ pg1.(evalid) -> pg1.(dst) e = pg2.(dst) e;
}.

Definition list_to_set {V: Type} (l: list V): V -> Prop := 
  fun v => In v l.

Definition graph_connected {V E: Type} (pg: PreGraph V E): Prop := 
  forall x y, pg.(vvalid) x -> pg.(vvalid) y -> connected pg x y.
  
Definition is_tree {V E: Type} (pg: PreGraph V E) (vl: list V) (el: list E): Prop := 
    length el + 1 = length vl /\
    graph_connected (Build_PreGraph V E vl el pg.(src) pg.(dst) pg.(weight)).

(**求列表和*)
Definition get_sum {V E: Type} (pg: PreGraph V E) (l: list E): Z :=
  fold_right Z.add 0%Z (map pg.(weight) l).

Definition is_spanning_tree {V E: Type} (pg: PreGraph V E) (vl: list V) (el: list E): Prop := 
  is_tree pg vl el /\ (list_to_set vl) == pg.(vvalid).

Definition is_minimal_spanning_tree {V E: Type} (pg: PreGraph V E) (vl: list V) (el: list E): Prop :=
  is_spanning_tree pg vl el /\ (forall vl' el', is_spanning_tree pg vl' el' -> (get_sum pg el <= get_sum pg el')%Z).

Theorem nonempty_finite_set_has_minimal: 
  forall (L: list Z) (A: Z -> Prop),
    (exists a, A a) -> 
    (forall a, A a -> In a L) -> 
    exists a, A a /\ (forall a', A a' -> a <= a')%Z.
Proof.
  induction L.
  + intros.
    destruct H as [a ?].
    specialize (H0 a).
    destruct H0; tauto.
  + intros.
    specialize (IHL A).
    Admitted.
    

Theorem finite_graph_has_finite_subgraphs {V E: Type}: 
  forall (pg: PreGraph V E), 
    exists subgl: list (PreGraph V E), (forall subg, In subg subgl <-> subgraph subg pg).
Proof.
  (* by induction *)
  Admitted.


Theorem spanning_tree_exists {V E: Type}:
  forall (pg: PreGraph V E), 
    graph_connected pg -> 
    exists vl el, is_spanning_tree pg vl el.
Proof.
  (* by induction. *)
  Admitted.

Theorem minimal_spanning_tree_exists {V E: Type}:
  forall (pg: PreGraph V E), 
    graph_connected pg ->
    exists vl el, is_minimal_spanning_tree pg vl el.
Proof.
  unfold is_minimal_spanning_tree.
  intros.
  pose proof (spanning_tree_exists pg H).
  pose proof (finite_graph_has_finite_subgraphs pg).
  destruct H1 as [subgl ?].
  pose proof (nonempty_finite_set_has_minimal (map (get_sum pg) (map get_edges subgl))).
  Admitted.

Record State (V E: Type) := 
{
  vertex_taken: list V;
  edge_taken: list E;
}.

Notation "s '.(vertex_taken)'" := (vertex_taken _ _ s) (at level 1).
Notation "s '.(edge_taken)'" := (edge_taken _ _ s) (at level 1).

Definition set_of_adjacent_edge_to_taken {V E: Type} (pg: PreGraph V E) (s: State V E): E -> Prop :=
  fun e => 
    pg.(evalid) e /\ 
    ((In (pg.(src) e) s.(vertex_taken) /\ ~ In (pg.(dst) e) s.(vertex_taken)) 
    \/ (In (pg.(dst) e) s.(vertex_taken) /\ ~ In (pg.(dst) e) s.(vertex_taken))).

Definition set_of_the_edges_want_to_add {V E: Type} (pg: PreGraph V E) (s: State V E): E -> Prop :=
  fun e => set_of_adjacent_edge_to_taken pg s e /\ 
  forall e', set_of_adjacent_edge_to_taken pg s e' -> (pg.(weight) e <= pg.(weight) e')%Z.

Definition set_of_the_vertices_want_to_add {V E: Type} (pg: PreGraph V E) (s: State V E) (e: E): V -> Prop :=
  fun v =>  
  ((pg.(src) e = v /\ In (pg.(dst) e) s.(vertex_taken)) \/ (pg.(dst) e = v /\ In (pg.(src) e) s.(vertex_taken))).

Definition add_the_edge_and_the_vertex {V E: Type} (pg: PreGraph V E) (e: E) (v: V): StateRelMonad.M (State V E) unit :=
  fun s1 _ s2 => 
    s2.(vertex_taken) = v :: s1.(vertex_taken) /\
    s2.(edge_taken) = e :: s1.(edge_taken).

Definition get_any_edge_in_edge_candidates {V E: Type} (pg: PreGraph V E): StateRelMonad.M (State V E) E :=
  fun s1 e s2 => 
    e ∈ set_of_the_edges_want_to_add pg s1 /\ s1 = s2.

Definition get_any_vertex_in_vertex_candidates {V E: Type} (pg: PreGraph V E) (e: E): StateRelMonad.M (State V E) V :=
  fun s1 v s2 => 
    v ∈ set_of_the_vertices_want_to_add pg s1 e /\ s1 = s2.

Import StateRelMonadOp.
    
(**开始定义算法过程*)
Definition body_prim {V E: Type} (pg: PreGraph V E): 
                unit -> StateRelMonad.M (State V E) (ContinueOrBreak unit unit) :=
      (**s1 是初始状态， s2 是返回后的状态*)
      (* edges_candidates <- (fun s1 tmp s2 => tmp = set_of_the_edges_want_to_add pg s1 /\ s1 = s2);; *)
      fun _ => choice (test (fun s1 => list_to_set s1.(vertex_taken) == pg.(vvalid));;
              break tt)
              (test (fun s1 => ~ (list_to_set s1.(vertex_taken) == pg.(vvalid)));;
              e <- get_any_edge_in_edge_candidates pg;;
              v <- get_any_vertex_in_vertex_candidates pg e;;
              add_the_edge_and_the_vertex pg e v;;
              continue tt).

Definition prim {V E: Type} (pg: PreGraph V E): unit -> StateRelMonad.M (State V E) unit :=
  fun _ => repeat_break (body_prim pg) tt.

(* 不变量 *)
(* 永远有一棵最小生成树包含以选的 *)
Definition I1 {V E: Type} (pg: PreGraph V E) (s: State V E): Prop :=
  exists vl el, is_minimal_spanning_tree pg vl el 
  /\ list_to_set s.(vertex_taken) ⊆ list_to_set vl /\ list_to_set s.(edge_taken) ⊆ list_to_set el.

(* 选的永远是一棵树 *)
Definition I2 {V E: Type} (pg: PreGraph V E) (s: State V E): Prop :=
  is_tree pg s.(vertex_taken) s.(edge_taken).

Lemma keep_I2 {V E: Type} (pg: PreGraph V E) (s1 s2: State V E):
    forall (u: V) (pg: PreGraph V E),
    pg.(vvalid) u ->
    graph_connected pg -> 
    Hoare (fun s => I2 pg s) 
          (body_prim pg tt)
          (fun res (s: State V E) => 
              match res with
              | by_continue _ => I2 pg s
              | by_break _ => I2 pg s
              end).
Proof.
  intros.
  unfold I2, body_prim.
  (* apply Hoare_choice. *)
Admitted.

(* 设{x,y}是新选的边，x在已选的里，y不在。 如果{x,y}在原来的最小生成树中，什么也不用干
如果不在，那么要修改这个最小生成树，要加上{x,y}，删掉一条边。
先来陈述找到这条要删的边的算法。 *)

(*  假设通过这个算法找到要删的边叫{u,v}，
1、要证明，删除u，v后，任意一点k，只用删除完生成树的边，要么和u连通，要么和v连通
   证明思路：未知
2、要证明：加上{x,y}后，u,v连通了
  证明思路：这跟{u,v}的构造有关
            先证明在y与x的在原先最小生成树的路径中，存在某一个边{u,v}，u还在已经选的树里，但v就不在了
            {u,v}的构造就选成这个。
            那么v->y（由构造）， y->x, x->u（已经选的是一棵树）。*)

(* Theorem find_the_edge_want_to_delete {V E: Type} (pg: PreGraph V E) (s: State V E) (e: E):
Proof.
  
Qed. *)



(* Theorem the_edge_want_to_delete {V E: Type} (s: State V E) (x y: V) (pg: PreGraph V E):

Proof.
  
Qed. *)



Theorem keep_I1 {V E: Type} (s1 s2: State V E):
  forall (u: V) (pg: PreGraph V E),
        pg.(vvalid) u -> 
        graph_connected pg -> 
        Hoare (fun s => I1 pg s) 
        (body_prim pg tt)
        (fun res (s: State V E) => 
            match res with
            | by_continue _ => I1 pg s
            | by_break _ => I1 pg s
            end).
Proof.
Admitted.

Lemma initial_state {V E: Type} (s: State V E):
    forall (u: V) (pg: PreGraph V E),
    pg.(vvalid) u ->
    graph_connected pg -> 
    s.(vertex_taken) = u :: nil /\ s.(edge_taken) = nil -> I1 pg s /\ I2 pg s.
Proof.
  intros u.
  unfold I1, I2, is_tree.
  intros.
  destruct H1 as [? ?].
  split.
  + pose proof (minimal_spanning_tree_exists pg H0).
    destruct H3 as [vl [el ?]].
    exists vl, el.
    split; auto.
    split.
    - intros v ?.
      unfold is_minimal_spanning_tree in H3.
      unfold is_spanning_tree in H3.
      destruct H3 as [[? ?] _].
      unfold is_tree in H3.
      destruct H3 as [? _].
      rewrite H1 in H4.
      unfold list_to_set in H4.
      simpl in H4.
      destruct H4; [| tauto].
      subst.
      apply H5.
      apply H.
    - rewrite H2.
      unfold list_to_set.
      simpl.
      sets_unfold; tauto.
  + split.
    - rewrite H1, H2.
      unfold length.
      lia.
Admitted.

Theorem prim_find_tree_if_break {V E: Type}:
  forall (u: V) (pg: PreGraph V E),
  pg.(vvalid) u ->
  graph_connected pg -> 
  Hoare (fun s0 => s0.(vertex_taken) = u :: nil /\ s0.(edge_taken) = nil)
        (prim pg tt)
        (fun (_: unit) (s: State V E) => 
            is_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
  intros.
  unfold prim.
  apply (Hoare_repeat_break (body_prim pg) (fun (_: unit) (s0: State V E) => s0.(vertex_taken) = u :: nil /\ s0.(edge_taken) = nil)         (fun (_: unit) (s: State V E) => 
  is_tree pg s.(vertex_taken) s.(edge_taken))).
  intros.
  unfold body_prim.
Admitted.



Theorem prim_find_spanning_tree_if_break {V E: Type}:
  forall (u: V) (pg: PreGraph V E),
    pg.(vvalid) u ->
    graph_connected pg -> 
    Hoare (fun s0 => s0.(vertex_taken) = u :: nil /\ s0.(edge_taken) = nil)
          (prim pg tt)
          (fun (_: unit) (s: State V E) => 
              is_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
  intros.
  unfold prim.
Admitted.



Theorem prim_functional_correctness_foundation {V E: Type}: 
    forall (u: V) (pg: PreGraph V E),
        pg.(vvalid) u ->
        graph_connected pg -> 
        Hoare (fun s => I1 pg s)
              (prim pg tt)
              (fun (_: unit) (s: State V E) => 
              is_minimal_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
Admitted.

Theorem prim_functional_correctness {V E: Type}:
    forall (u: V) (pg: PreGraph V E),
      pg.(vvalid) u ->
      graph_connected pg -> 
      Hoare (fun s0 => s0.(vertex_taken) = u :: nil /\ s0.(edge_taken) = nil)
            (prim pg tt)
            (fun (_: unit) (s: State V E) => 
                is_minimal_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
Admitted.



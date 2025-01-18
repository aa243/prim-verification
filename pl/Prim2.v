Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
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
  NoDup pg.(vertices) /\ NoDup pg.(edges) /\
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

Lemma step_symmetric {V E: Type}:
  forall (pg: PreGraph V E) (x y: V),
    step pg x y -> step pg y x.
Proof.
  intros.
  unfold step in *.
  destruct H as [e ?].
  exists e.
  tauto.
Qed.


Lemma step_on_one_edge {V E: Type}:
  forall (pg: PreGraph V E) (e: E),
    is_legal_graph pg ->
    pg.(evalid) e -> 
    step pg (pg.(src) e) (pg.(dst) e).
Proof.
  intros.
  unfold step.
  exists e.
  left.
  unfold is_legal_graph in H.
  destruct H.
  destruct H1.
  specialize (H2 e H0).
  destruct H2.
  constructor; auto.
Qed.


Record subgraph {V E: Type} (pg1 pg2: PreGraph V E): Prop :=
{
  subgraph_legal: is_legal_graph pg1;
  biggraph_legal: is_legal_graph pg2;
  subgraph_vvalid: pg1.(vvalid) ⊆ pg2.(vvalid);
  subgraph_evalid: pg1.(evalid) ⊆ pg2.(evalid);
  subgraph_src: forall e, e ∈ pg1.(evalid) -> pg1.(src) e = pg2.(src) e;
  subgraph_dst: forall e, e ∈ pg1.(evalid) -> pg1.(dst) e = pg2.(dst) e;
}.

Definition list_to_set {V: Type} (l: list V): V -> Prop := 
  fun v => In v l.

Definition graph_connected {V E: Type} (pg: PreGraph V E): Prop := 
  is_legal_graph pg /\ (forall x y, pg.(vvalid) x -> pg.(vvalid) y -> connected pg x y).


(* connected x y -> connected y x *)
Theorem connected_symmetric {V E: Type}:
  forall (pg: PreGraph V E) x y, connected pg x y -> connected pg y x.
Proof.
  unfold connected.
  intros.
  induction_1n H.
  + reflexivity.
  + assert (step pg x0 x).
    {
      unfold step in H0.
      unfold step.
      destruct H0 as [e ?].
      exists e.
      destruct H0.
      + right.
        destruct H0.
        split.
        - tauto.
        - tauto.
        - tauto.
        - tauto.
        - tauto.
      + left.
        destruct H0.
        split.
        - tauto.
        - tauto.
        - tauto.
        - tauto.
        - tauto.
    }
  transitivity_n1 x0.
  * tauto.
  * tauto.
Qed.

(* 子图中x,y连通，则大图中x,y连通 *)
Theorem connected_in_subgraph_then_connected_in_graph {V E: Type}:
  forall (subg pg: PreGraph V E) x y, subgraph subg pg -> connected subg x y -> connected pg x y.
Proof.
  intros.
  assert (step subg ⊆ step pg).
  { 
    destruct H.
    unfold step.
    sets_unfold.
    intros.
    destruct H as [e ?].
    exists e.
    destruct H.
    + left.
      destruct H.
      split.
      - sets_unfold in subgraph_evalid0.
        specialize (subgraph_evalid0 e).
        tauto. 
      - sets_unfold in subgraph_vvalid0.
        specialize (subgraph_vvalid0 a).
        tauto.
      - sets_unfold in subgraph_vvalid0.
        specialize (subgraph_vvalid0 a0).
        tauto.
      - specialize (subgraph_src0 e).
        pose proof subgraph_src0 step_evalid0.
        rewrite <- H.
        tauto.
      - specialize (subgraph_dst0 e).
        pose proof subgraph_dst0 step_evalid0.
        rewrite <- H.
        tauto.
    + right.
      destruct H.
      split.
      - sets_unfold in subgraph_evalid0.
        specialize (subgraph_evalid0 e).
        tauto. 
      - sets_unfold in subgraph_vvalid0.
        specialize (subgraph_vvalid0 a0).
        pose proof subgraph_vvalid0 step_src_valid0.
        tauto.
      - sets_unfold in subgraph_vvalid0.
        specialize (subgraph_vvalid0 a).
        pose proof subgraph_vvalid0 step_dst_valid0.
        tauto.
      - specialize (subgraph_src0 e).
        pose proof subgraph_src0 step_evalid0.
        rewrite <- H.
        tauto.
      - specialize (subgraph_dst0 e).
        pose proof subgraph_dst0 step_evalid0.
        rewrite <- H.
        tauto.
  }
  unfold connected.
  unfold connected in H0.
  induction_1n H0.
  + reflexivity.
  + specialize (H1 x x0).
    assert (step subg ⊆ step pg).
    { 
      destruct H.
      unfold step.
      sets_unfold.
      intros.
      destruct H as [e ?].
      exists e.
      destruct H.
      + left.
        destruct H.
        split.
        - sets_unfold in subgraph_evalid0.
          specialize (subgraph_evalid0 e).
          tauto. 
        - sets_unfold in subgraph_vvalid0.
          specialize (subgraph_vvalid0 a).
          tauto.
        - sets_unfold in subgraph_vvalid0.
          specialize (subgraph_vvalid0 a0).
          tauto.
        - specialize (subgraph_src0 e).
          pose proof subgraph_src0 step_evalid0.
          rewrite <- H.
          tauto.
        - specialize (subgraph_dst0 e).
          pose proof subgraph_dst0 step_evalid0.
          rewrite <- H.
          tauto.
      + right.
        destruct H.
        split.
        - sets_unfold in subgraph_evalid0.
          specialize (subgraph_evalid0 e).
          tauto. 
        - sets_unfold in subgraph_vvalid0.
          specialize (subgraph_vvalid0 a0).
          pose proof subgraph_vvalid0 step_src_valid0.
          tauto.
        - sets_unfold in subgraph_vvalid0.
          specialize (subgraph_vvalid0 a).
          pose proof subgraph_vvalid0 step_dst_valid0.
          tauto.
        - specialize (subgraph_src0 e).
          pose proof subgraph_src0 step_evalid0.
          rewrite <- H.
          tauto.
        - specialize (subgraph_dst0 e).
          pose proof subgraph_dst0 step_evalid0.
          rewrite <- H.
          tauto.
    }
    specialize (IHrt pg).
    pose proof IHrt H H3.
    pose proof H1 H2.
    transitivity x0; [ | tauto].
    transitivity_1n x0.
    * tauto.
    * reflexivity.
Qed.

Definition reachable_via_sets {V E} (pg: PreGraph V E) (P: V -> Prop):
  V -> V -> Prop :=
  clos_refl_trans (fun x y => step pg x y /\ P y).

(** 又需要补充_[reachable_via_sets]_的代数性质。*)

#[export] Instance reachable_via_sets_mono {V E} (pg: PreGraph V E):
  Proper (Sets.included ==> Sets.included) (reachable_via_sets pg).
Proof.
  unfold Proper, respectful.
  intros.
  sets_unfold; intros u v ?.
  induction_1n H0.
  + reflexivity.
  + destruct H1.
    apply H in H2.
    transitivity_1n u0.
    - tauto.
    - apply IHrt; tauto.
Qed.

#[export] Instance reachable_via_sets_congr {V E} (pg: PreGraph V E):
  Proper (Sets.equiv ==> Sets.equiv) (reachable_via_sets pg).
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_equiv_Sets_included; split;
    apply reachable_via_sets_mono.
  + rewrite H; reflexivity.
  + rewrite H; reflexivity.
Qed.

#[export] Instance reachable_via_sets_congr' {V E} (pg: PreGraph V E):
  Proper (Sets.equiv ==> eq ==> eq ==> iff) (reachable_via_sets pg).
Proof.
  unfold Proper, respectful; intros; subst.
  apply reachable_via_sets_congr.
  tauto.
Qed.

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

Definition reachable_via_lists {V E} (pg: PreGraph V E) (P: list V): V -> V -> Prop :=
  clos_refl_trans (fun x y => step pg x y /\ In y P).

Definition is_new_list_delete_one_from_original {A} (l: list A) (a: A): list A -> Prop :=
  fun l' => forall x, In x l' <-> In x l /\ ~ x = a.

Lemma deleted_list_exists {A} (l: list A) (a: A):
  NoDup l -> In a l -> exists l', length l' + 1 = length l /\ NoDup l' 
/\ is_new_list_delete_one_from_original l a l' .
Proof.
Admitted.
  
Lemma deleted_list_exists_with_sum_equal {V E} (pg: PreGraph V E) (l: list E) (a: E):
  NoDup l -> In a l -> 
  exists l', Z.add (get_sum pg l') (pg.(weight) a) = (get_sum pg l)
  /\ length l' + 1 = length l /\ NoDup l' 
  /\ is_new_list_delete_one_from_original l a l' .
Proof.
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
    \/ (In (pg.(dst) e) s.(vertex_taken) /\ ~ In (pg.(src) e) s.(vertex_taken))).

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

(* 选了所有点 *)
Definition I3 {V E: Type} (pg: PreGraph V E) (s: State V E): Prop :=
  list_to_set s.(vertex_taken) == pg.(vvalid).

(* Lemma Nodup_empty_list:
  NoDup []%list. *)

(* Level 1 *)
(* 初始状态满足 I2 *)
Lemma initial_state_to_I2 {V E: Type} (s: State V E):
  forall (u: V) (pg: PreGraph V E),
  pg.(vvalid) u ->
  graph_connected pg -> 
  s.(vertex_taken) = u :: nil /\ s.(edge_taken) = nil -> I2 pg s.
Proof.
intros.
unfold I2.
unfold is_tree.
destruct H1 as [? ?].
rewrite H2.
rewrite H1.
simpl.
split; [ lia | ].
unfold graph_connected.
split.
+ unfold is_legal_graph.
  intros.
  split; [ | split];[  simpl; apply NoDup_cons | simpl; apply NoDup_nil | ]; [ simpl; tauto| apply NoDup_nil |].
  intros.
  assert (~ {|
    vertices := [u];
    edges := [];
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |}.(evalid) e).
  {
    unfold evalid.
    tauto. 
  }
  tauto.
+
  intros.
  unfold connected.
  assert (In x [u]).
  {
    apply H3.
  }
  assert (In y [u]).
  {
    apply H4. 
  }
  assert (x = u).
  {
    simpl in H5.
    destruct H5; [rewrite H5 ; reflexivity| tauto].
  }
  assert (y = u).
  {
    simpl in H6.
    destruct H6; [rewrite H6 ; reflexivity| tauto].
  }
  subst.
  reflexivity.
Qed.

(* Level 1 *)
(* 辅助工具用来解析Hoare *)
Theorem Hoare_get_any_edge_in_edge_candidates {V E: Type}:
  forall (pg: PreGraph V E) (P: State V E -> Prop),
  Hoare P (get_any_edge_in_edge_candidates pg) (fun e s => set_of_the_edges_want_to_add pg s e /\ P s).
Proof.
  intros.
  unfold Hoare, get_any_edge_in_edge_candidates.
  intros.
  destruct H0.
  subst.
  tauto.
Qed.

(* Level 1 *)
(* 辅助工具用来解析Hoare *)
Theorem Hoare_get_any_vertex_in_vertex_candidates {V E: Type}:
  forall (pg: PreGraph V E) (e: E) (P: State V E -> Prop),
  Hoare P (get_any_vertex_in_vertex_candidates pg e) (fun v s => set_of_the_vertices_want_to_add pg s e v /\ P s).
Proof.
  intros.
  unfold Hoare, get_any_vertex_in_vertex_candidates.
  intros.
  destruct H0.
  subst.
  tauto.
Qed.

(* Level 1 *)
(* 每一步选出来的图都是合法的 *)
Theorem keep_chosen_graph_legal {V E: Type}:
  forall (pg: PreGraph V E) (σ1 σ2: State V E) (e: E) (v: V),
  graph_connected pg -> 
  set_of_the_edges_want_to_add pg σ1 e ->
  set_of_the_vertices_want_to_add pg σ1 e v ->
  σ2.(vertex_taken) = v :: σ1.(vertex_taken) ->
  σ2.(edge_taken) = e :: σ1.(edge_taken) ->
  is_legal_graph {|
    vertices := σ1.(vertex_taken);
    edges := σ1.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |} ->
  is_legal_graph {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |}.
Proof.
intros.
unfold set_of_the_edges_want_to_add in H0.
unfold graph_connected in H.
destruct H as [H L].
clear L.
destruct H0.
clear H5.
unfold set_of_adjacent_edge_to_taken in H0.
destruct H0.
unfold set_of_the_vertices_want_to_add in H1.
assert (In v σ2.(vertex_taken)).
{ rewrite H2. simpl. tauto. }
assert (In e σ2.(edge_taken)).
{ rewrite H3. simpl. tauto. }
unfold is_legal_graph.
split.
+ simpl.
  unfold is_legal_graph in H.
  destruct H.
  unfold is_legal_graph in H4.
  destruct H4.
  simpl in H4.
  destruct H1.
    * destruct H5.
      **  destruct H5.
          destruct H1.
          rewrite H1 in H5. 
          tauto.
      **  destruct H5. 
          destruct H1.
          rewrite H1 in H10.
          rewrite H2.
          apply NoDup_cons.
          -- tauto.
          -- tauto.
    * destruct H5.
      **  destruct H5.
          destruct H1.
          rewrite H1 in H10.
          rewrite H2.
          apply NoDup_cons.
          -- tauto.
          -- tauto. 
      **  destruct H5. 
          destruct H1.
          rewrite H1 in H5.
          rewrite H2.
          apply NoDup_cons.
          -- tauto.
          -- tauto.
+ split.
  - simpl.
    unfold is_legal_graph in H.
    destruct H.
    destruct H8.
    unfold is_legal_graph in H4.
    destruct H4.
    destruct H10.
    simpl in H10.
    destruct H1.
    ++
      destruct H5.
      ** destruct H5.
         destruct H1.
         rewrite H1 in H5.
         tauto.
      ** destruct H5.
         destruct H1.
         change ({|
         vertices := σ1.(vertex_taken);
         edges := σ1.(edge_taken);
         src := pg.(src);
         dst := pg.(dst);
         weight := pg.(weight)
       |}.(vertices)) with (σ1.(vertex_taken)) in H4.
       rewrite H3.
       apply NoDup_cons;[ | tauto ].
       destruct 
       (classic (In e σ1.(edge_taken))).
       *** 
           specialize (H11 e H14).
           destruct H11.
           tauto.
       *** tauto.
    ++ destruct H5.
      **  destruct H5.
         destruct H1.
         change ({|
         vertices := σ1.(vertex_taken);
         edges := σ1.(edge_taken);
         src := pg.(src);
         dst := pg.(dst);
         weight := pg.(weight)
       |}.(vertices)) with (σ1.(vertex_taken)) in H4.
       rewrite H3.
       apply NoDup_cons;[ | tauto ].
       destruct 
       (classic (In e σ1.(edge_taken))).
       *** 
           specialize (H11 e H14).
           destruct H11.
           tauto.
       *** tauto.
      ** destruct H5.
         destruct H1.
         rewrite H1 in H5.
         tauto.
  -
  intros.
  change ({|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |}.(evalid) e0) with (In e0 σ2.(edge_taken)) in H8.
  rewrite H3 in H8.
  simpl in H8.
  change ({|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
    |}.(vvalid)
    ({|
      vertices := σ2.(vertex_taken);
      edges := σ2.(edge_taken);
      src := pg.(src);
      dst := pg.(dst);
      weight := pg.(weight)
    |}.(src) e0)) with (In (pg.(src) e0) σ2.(vertex_taken)).
  change ({|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
    |}.(vvalid)
    ({|
      vertices := σ2.(vertex_taken);
      edges := σ2.(edge_taken);
      src := pg.(src);
      dst := pg.(dst);
      weight := pg.(weight)
    |}.(dst) e0)) with (In (pg.(dst) e0) σ2.(vertex_taken)).
    unfold is_legal_graph in H4.
  destruct H8.
  *** subst e0.
    destruct H5.
    +++ destruct H5.
      destruct H1; [tauto |].
      destruct H1.
      split.
      ++++ rewrite H2.
        simpl.
        tauto.
      ++++ rewrite H2, H1.
          simpl.
          tauto.
    +++ destruct H5.
      destruct H1; [ | tauto].
      destruct H1.
      split.
      ++++ rewrite H2, H1.
        simpl.
        tauto.
      ++++ rewrite H2.
          simpl.
          tauto. 
  *** destruct H5.
    +++ destruct H5.
      destruct H1; [ tauto | ].
      destruct H1.
      destruct H4.
      destruct H11.
      specialize (H12 e0 H8).
      rewrite H2.
      simpl.
      tauto.
    +++ destruct H5.
      destruct H1; [ | tauto].
      destruct H1.
      destruct H4.
      destruct H11.
      specialize (H12 e0 H8).
      rewrite H2.
      simpl.
      tauto. 
Qed.

Theorem keep_chosen_graph_subgraph {V E: Type}:
  forall (pg: PreGraph V E) (σ1 σ2: State V E) (e: E) (v: V),
  graph_connected pg -> 
  set_of_the_edges_want_to_add pg σ1 e ->
  set_of_the_vertices_want_to_add pg σ1 e v ->
  σ2.(vertex_taken) = v :: σ1.(vertex_taken) ->
  σ2.(edge_taken) = e :: σ1.(edge_taken) ->
  subgraph {|
    vertices := σ1.(vertex_taken);
    edges := σ1.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |} pg ->
  subgraph {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |} pg.
Proof.
Admitted.



(* Level 1 *)
(* 每一步新加的v与选出来的点用选的边连通 *)
Lemma vertices_candidate_is_connected {V E: Type}:
  (* v是candiate， u是任意一点，u和v是连通的。 *)
  forall (pg: PreGraph V E) (σ1 σ2: State V E) (e: E) (v: V) (u: V),
  graph_connected pg -> 
  set_of_the_edges_want_to_add pg σ1 e ->
  set_of_the_vertices_want_to_add pg σ1 e v ->
  σ2.(vertex_taken) = v :: σ1.(vertex_taken) ->
  σ2.(edge_taken) = e :: σ1.(edge_taken) ->
  is_tree pg σ1.(vertex_taken) σ1.(edge_taken) ->
  In u σ2.(vertex_taken) ->
  connected
  {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |} v u.
Proof.
  intros.
  pose proof H0 as P0.
  unfold set_of_the_edges_want_to_add in H0.
  pose proof H as P.
  unfold graph_connected in H.
  destruct H as [H L].
  unfold connected.
  unfold set_of_the_edges_want_to_add in H0.
  destruct H0.
  clear H6.
  unfold set_of_adjacent_edge_to_taken in H0.
  destruct H0.
  pose proof H1 as P1.
  unfold set_of_the_vertices_want_to_add in H1.
  unfold is_tree in H4.
  destruct H4.
  clear H4.
  unfold graph_connected in H7.
  assert (In v σ2.(vertex_taken)).
  { rewrite H2. simpl. tauto. }
  assert (In e σ2.(edge_taken)).
  { rewrite H3. simpl. tauto. }
  assert (pg.(src) = {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |}.(src) ).
  { reflexivity. }
  assert (pg.(dst) = {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |}.(dst) ). { reflexivity. }
  rewrite H2 in H5.
  simpl in H5.
  destruct H5.
  * rewrite H5; reflexivity.
  * destruct H7.
   destruct H1.
    - destruct H1.
      destruct H6; [ tauto | ].
      destruct H6 as [H6 M]. 
      assert (is_legal_graph
      {|
        vertices := σ2.(vertex_taken);
        edges := σ2.(edge_taken);
        src := pg.(src);
        dst := pg.(dst);
        weight := pg.(weight)
      |}).
      { rewrite H3.
        pose proof keep_chosen_graph_legal pg σ1 σ2 e v.
        rewrite <- H3.
        apply H13;[ tauto | tauto | tauto | tauto | tauto | tauto ].
        }
      transitivity_1n (pg.(dst) e).
      + rewrite <- H1.
        rewrite H9, H10.
        apply (step_on_one_edge _ e); [ | apply H8].
        rewrite <- H10.
        rewrite <- H9.
        tauto.
      + specialize (H11 (pg.(dst) e) u H6 H5).
        change (clos_refl_trans
        (step
           {|
             vertices := σ2.(vertex_taken);
             edges := σ2.(edge_taken);
             src := pg.(src);
             dst := pg.(dst);
             weight := pg.(weight)
           |}) (pg.(dst) e) u) with (connected {|
             vertices := σ2.(vertex_taken);
             edges := σ2.(edge_taken);
             src := pg.(src);
             dst := pg.(dst);
             weight := pg.(weight)
            |} (pg.(dst) e) u).
          apply (connected_in_subgraph_then_connected_in_graph {|
            vertices := σ1.(vertex_taken);
            edges := σ1.(edge_taken);
            src := pg.(src);
            dst := pg.(dst);
            weight := pg.(weight)
          |} _ (pg.(dst) e) u); [ | apply H11].
          split; [ apply H7 | apply H13 | sets_unfold; rewrite H2; simpl | sets_unfold; rewrite H3; simpl | intros; reflexivity | intros; reflexivity].
          ++ intros.
            change ({|
              vertices := v :: σ1.(vertex_taken);
              edges := σ2.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight)
            |}.(vvalid) a) with (In a (v :: σ1.(vertex_taken))).
            simpl; tauto.
          ++ intros.
            change ({|
              vertices := σ2.(vertex_taken);
              edges := e :: σ1.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight)
            |}.(evalid) a) with (In a (e :: σ1.(edge_taken))).
            simpl; tauto.
    - destruct H1.
      destruct H6; [ | tauto ].
      destruct H6 as [H6 M]. 
      assert (is_legal_graph
      {|
        vertices := σ2.(vertex_taken);
        edges := σ2.(edge_taken);
        src := pg.(src);
        dst := pg.(dst);
        weight := pg.(weight)
      |}).
      { rewrite H3.
        pose proof 
        keep_chosen_graph_legal pg σ1 σ2 e v.
        rewrite <- H3.
        apply H13;[ tauto | tauto | tauto | tauto | tauto | tauto ].
        }
      transitivity_1n (pg.(src) e).
      + rewrite <- H1.
        apply step_symmetric.
        rewrite H9, H10.
        apply (step_on_one_edge _ e); [ | apply H8 ].
        rewrite <- H10.
        rewrite <- H9.
        tauto.
      + specialize (H11 (pg.(src) e) u H6 H5).
        change (clos_refl_trans
        (step
          {|
            vertices := σ2.(vertex_taken);
            edges := σ2.(edge_taken);
            src := pg.(src);
            dst := pg.(dst);
            weight := pg.(weight)
          |}) (pg.(src) e) u) with (connected {|
            vertices := σ2.(vertex_taken);
            edges := σ2.(edge_taken);
            src := pg.(src);
            dst := pg.(dst);
            weight := pg.(weight)
            |} (pg.(src) e) u).
          apply (connected_in_subgraph_then_connected_in_graph {|
            vertices := σ1.(vertex_taken);
            edges := σ1.(edge_taken);
            src := pg.(src);
            dst := pg.(dst);
            weight := pg.(weight)
          |} _ (pg.(src) e) u); [ | apply H11].
          split; [ apply H7 | apply H13 | sets_unfold; rewrite H2; simpl | sets_unfold; rewrite H3; simpl | intros; reflexivity | intros; reflexivity].
          ++ intros.
            change ({|
              vertices := v :: σ1.(vertex_taken);
              edges := σ2.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight)
            |}.(vvalid) a) with (In a (v :: σ1.(vertex_taken))).
            simpl; tauto.
          ++ intros.
            change ({|
              vertices := σ2.(vertex_taken);
              edges := e :: σ1.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight)
            |}.(evalid) a) with (In a (e :: σ1.(edge_taken))).
            simpl; tauto.
  
Qed.

(* Level 1 *)
(* 要求一的命题：每次选的都是一棵树 *)
Theorem Hoare_add_the_edge_and_the_vertex_for_istree {V E: Type}:
  forall (pg: PreGraph V E) (e: E) (v: V),
  graph_connected pg ->
  Hoare
  (fun s : State V E =>
   set_of_the_vertices_want_to_add pg s e v /\
   set_of_the_edges_want_to_add pg s e /\
   ~ list_to_set s.(vertex_taken) == pg.(vvalid) /\
   is_tree pg s.(vertex_taken) s.(edge_taken))
  (add_the_edge_and_the_vertex pg e v)
  (fun _ s => is_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
  intros.
  unfold Hoare, add_the_edge_and_the_vertex.
  intros; clear a.
  destruct H1.
  destruct H0.
  destruct H3.
  destruct H3.
  pose proof H5 as L.
  clear H5.
  destruct H4. 
  unfold is_tree in *.
  destruct H5.
  split.
  + rewrite H1, H2.
    simpl.
    rewrite H5.
    lia.
  + unfold graph_connected.
    split.
    **
    apply (keep_chosen_graph_legal pg σ1 σ2 e v); [tauto | unfold set_of_the_edges_want_to_add; tauto | tauto | tauto | tauto | unfold graph_connected in H6; tauto]. 
    ** intros.
       change ({|
        vertices := σ2.(vertex_taken);
        edges := σ2.(edge_taken);
        src := pg.(src);
        dst := pg.(dst);
        weight := pg.(weight)
      |}.(vvalid) x) with (In x σ2.(vertex_taken)) in H7.
        change ({|
          vertices := σ2.(vertex_taken);
          edges := σ2.(edge_taken);
          src := pg.(src);
          dst := pg.(dst);
          weight := pg.(weight)
        |}.(vvalid) y) with (In y σ2.(vertex_taken)) in H8.
        rewrite H1 in H7.
        rewrite H1 in H8.
        simpl in H7, H8.
        destruct H7, H8.
        ++ subst; reflexivity.
        ++ subst x.
            apply (vertices_candidate_is_connected pg σ1 σ2 e v y); [tauto | unfold set_of_the_edges_want_to_add; tauto | tauto | tauto | tauto | unfold is_tree; tauto | rewrite H1; simpl; right; tauto].
        ++ subst y.
          apply (connected_symmetric _ v x).
          apply (vertices_candidate_is_connected pg σ1 σ2 e v x); [tauto | unfold set_of_the_edges_want_to_add; tauto | tauto | tauto | tauto | unfold is_tree; tauto | rewrite H1; simpl; right; tauto].
        ++ destruct H6.
        apply (connected_in_subgraph_then_connected_in_graph {|
          vertices := σ1.(vertex_taken);
          edges := σ1.(edge_taken);
          src := pg.(src);
          dst := pg.(dst);
          weight := pg.(weight)
        |} _ x y).
          -- split; [ tauto | 
          apply (keep_chosen_graph_legal pg σ1 σ2 e v); [tauto | unfold set_of_the_edges_want_to_add; tauto | tauto | tauto | tauto | unfold graph_connected in H6; tauto]
          | sets_unfold; rewrite H1; simpl | sets_unfold; rewrite H2; simpl | intros | intros ].
            +++ intros.
              change ({|
                vertices := v :: σ1.(vertex_taken);
                edges := σ2.(edge_taken);
                src := pg.(src);
                dst := pg.(dst);
                weight := pg.(weight)
              |}.(vvalid) a) with (In a (v :: σ1.(vertex_taken))).
              simpl; tauto.
            +++ intros.
              change ({|
                vertices := σ2.(vertex_taken);
                edges := e :: σ1.(edge_taken);
                src := pg.(src);
                dst := pg.(dst);
                weight := pg.(weight)
              |}.(evalid) a) with (In a (e :: σ1.(edge_taken))).
              simpl; tauto.
            +++ reflexivity.
            +++ reflexivity.
          -- specialize (H9 x y H7 H8).
            tauto.
Qed.

(* Level 1 *)
(* 若上一步的状态满足I2，则经过一步 primbody 之后的状态仍然满足I2 *)
Lemma keep_I2 {V E: Type} (pg: PreGraph V E):
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
  apply Hoare_choice.
  + apply Hoare_test_bind.
    intros.
    apply Hoare_ret'.
    intros.
    tauto.
  + apply Hoare_test_bind.
    eapply Hoare_bind.
    * apply (Hoare_get_any_edge_in_edge_candidates pg _).
    * intros e.
      eapply Hoare_bind.
      ++ apply (Hoare_get_any_vertex_in_vertex_candidates pg e _).
      ++ intros v.
          eapply Hoare_bind; [ | intros; apply Hoare_ret'].
          +++ apply (Hoare_add_the_edge_and_the_vertex_for_istree pg e v).
              tauto.
          +++ intros. 
              simpl in H0.
              tauto.
Qed.

(* Level 1 *)
(* 如果初始状态满足I2，那么prim得到的结果也满足I2 *)
Theorem prim_find_tree_if_break_f {V E: Type}:
  forall (pg: PreGraph V E),
  graph_connected pg -> 
  Hoare (fun s0 => I2 pg s0)
        (prim pg tt)
        (fun (_: unit) (s: State V E) => 
        I2 pg s).
Proof.
  intros.
  unfold prim.
  apply (Hoare_repeat_break (body_prim pg) 
                            (fun (_: unit) (s0: State V E) => I2 pg s0)
                            (fun (_: unit) (s: State V E) => 
                            I2 pg s)).
  intros.
  apply (keep_I2 pg ).
  apply H.
Qed.

(* Level 2 *)
(* 如果初始状态满足I2，那么执行 prim_body 后的状态若 continue 则满足I2，
   若 break 则满足I3 *)
Lemma break_with_I3 {V E: Type} (pg: PreGraph V E):
  forall (pg: PreGraph V E),
  graph_connected pg ->
  Hoare (fun s => I2 pg s)
        (body_prim pg tt)
        (fun res (s: State V E) =>
            match res with
            | by_continue _ => I2 pg s
            | by_break _ => I3 pg s
            end).
Proof.
  intros.
  unfold body_prim.
  apply Hoare_choice.
  + apply Hoare_test_bind.
    unfold I3.
    apply Hoare_ret'.
    tauto.
  + apply Hoare_test_bind.
    unfold I3.
    eapply Hoare_bind; [ apply Hoare_get_any_edge_in_edge_candidates | ].
    intros e.
    eapply Hoare_bind; [ apply Hoare_get_any_vertex_in_vertex_candidates | ].
    intros v.
    eapply Hoare_bind; [ | intros; apply Hoare_ret'].
    * apply (Hoare_add_the_edge_and_the_vertex_for_istree pg0 e v).
      tauto.
    * intros.
      simpl in H0.
      unfold I2.
      tauto.
Qed.

(* Level 2 *)
(* 如果初始状态满足I2，那么prim得到的结果满足I3 *)
Theorem prim_find_all_vertices_if_break_f {V E: Type}:
  forall (pg: PreGraph V E),
  graph_connected pg -> 
  Hoare (fun s0 => I2 pg s0)
        (prim pg tt)
        (fun (_: unit) (s: State V E) => 
            I3 pg s).
Proof.
  intros.
  unfold prim.
  apply (Hoare_repeat_break (body_prim pg) 
                            (fun (_: unit) (s0: State V E) => I2 pg s0)
                            (fun (_: unit) (s: State V E) => 
                              I3 pg s)).
  intros.
  apply (break_with_I3 pg ).
  apply H.
Qed.

(* Level 2 *)
(* 如果初始状态满足I2，那么prim得到的结果是原图的生成树 *)
Theorem prim_find_spanning_tree_if_break_f {V E: Type}:
  forall (pg: PreGraph V E),
    graph_connected pg -> 
    Hoare (fun s0 => I2 pg s0)
          (prim pg tt)
          (fun (_: unit) (s: State V E) => 
              is_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
  intros.
  unfold is_spanning_tree.
  pose proof (prim_find_tree_if_break_f pg H).
  pose proof (prim_find_all_vertices_if_break_f pg H).
  unfold I2 in H0,H1.
  unfold I3 in H1.
  unfold I2.
  unfold Hoare.
  unfold Hoare in H0, H1.
  intros.
  specialize (H0 σ1 a σ2).
  specialize (H1 σ1 a σ2).
  pose proof H0 H2 H3.
  pose proof H1 H2 H3.
  tauto.
Qed.

(* Level 2 *)
(* 从任意一点出发，prim 算法得到的结果都是原图的生成树 *)
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
  unfold Hoare.
  pose proof (prim_find_spanning_tree_if_break_f pg H0).
  unfold Hoare in H1.
  intros σ1 a σ2.
  specialize (H1 σ1 a σ2).
  pose proof (initial_state_to_I2 σ1 u pg).
  pose proof H2 H H0.
  intros.
  pose proof (H3 H4).
  pose proof (H1 H6 H5).
  tauto.
Qed.

(* 设{u,v}是新选的边，u在已选的里，v不在。 如果{u,v}在原来的最小生成树中，什么也不用干
如果不在，那么要修改这个最小生成树，要加上{u,v}，删掉一条边。
先来陈述找到这条要删的边的算法。 *)

(*  假设通过这个算法找到要删的边叫{x,y}，
1、要证明，删除x,y后，任意一点k，只用删除完生成树的边，要么和x连通，要么和y连通
   证明思路：未知
2、要证明：加上{u,v}后，x,y连通了
  证明思路：这跟{x,y}的构造有关
            先证明在v与u的在原先最小生成树的路径中，存在某一个边{x,y}，x还在已经选的树里，但y就不在了
            {x,y}的构造就选成这个。
            那么y->v（由构造）， v->u, u->x（已经选的是一棵树）。*)
  
Definition is_graph_after_delete {V E} (pg: PreGraph V E) (vl: list V) (el: list E) (e: E): list V -> list E -> Prop :=
  fun vl' el' => is_new_list_delete_one_from_original el e el' /\ vl = vl'.

Lemma graph_after_delete_exists {V E: Type}:
  forall (pg: PreGraph V E) (vl: list V) (el: list E) (e: E),
    is_minimal_spanning_tree pg vl el ->
    In e el ->
    exists vl' el', is_graph_after_delete pg vl el e vl' el'.
Proof.
  intros.
  unfold is_graph_after_delete.
  destruct H as [[[_ [[? [? ?]] _]] _] _].
  pose proof (deleted_list_exists el e ).
Admitted.
  

Theorem either_with_x_or_with_y {V E: Type}:
  forall (pg: PreGraph V E) (vl: list V) (el: list E) (e: E) (x y k: V) 
  (vl': list V) (el': list E),
    graph_connected pg ->
    is_minimal_spanning_tree pg vl el ->
    In e el ->
    is_graph_after_delete pg vl el e vl' el' ->
    pg.(vvalid) k ->
    (x = pg.(src) e /\ y = pg.(dst) e) \/ (x = pg.(dst) e /\ y = pg.(src) e) ->
    connected {|
      vertices := vl';
      edges := el';
      src := pg.(src);
      dst := pg.(dst);
      weight := pg.(weight)
    |} x k \/ connected {|
      vertices := vl';
      edges := el';
      src := pg.(src);
      dst := pg.(dst);
      weight := pg.(weight)
    |} y k.
Proof.
Admitted.

Theorem intermediate_point_between_x_and_y {V E: Type}:
  forall (pg: PreGraph V E) (s: State V E) (e: E) (v: V) (vl: list V) (el: list E),
    graph_connected pg ->
    set_of_the_vertices_want_to_add pg s e v ->
    set_of_the_edges_want_to_add pg s e -> 
    ~ list_to_set s.(vertex_taken) == pg.(vvalid) ->
    is_minimal_spanning_tree pg vl el ->
    list_to_set s.(vertex_taken) ⊆ list_to_set vl ->
    list_to_set s.(edge_taken) ⊆ list_to_set el ->
    (exists f x, 
    (x = pg.(src) f \/ x = pg.(dst) f) /\
    In f el /\ ~ In f s.(edge_taken) /\
    In x s.(vertex_taken) /\
    reachable_via_sets {|
      vertices := vl;
      edges := el;
      src := pg.(src);
      dst := pg.(dst);
      weight := pg.(weight)
    |} (Sets.complement (list_to_set s.(vertex_taken))) x v /\
    ( forall vl' el', is_graph_after_delete pg vl el f vl' el' ->
      is_minimal_spanning_tree pg vl' (e :: el'))
    ).
Proof.
Admitted.

Theorem Hoare_add_the_edge_and_the_vertex_for_ismst {V E: Type}:
  forall (pg: PreGraph V E) (e: E) (v: V),
  graph_connected pg ->
  Hoare
  (fun s : State V E =>
  set_of_the_vertices_want_to_add pg s e v /\
  set_of_the_edges_want_to_add pg s e /\
  ~ list_to_set s.(vertex_taken) == pg.(vvalid) /\
  (exists (vl : list V) (el : list E),
      is_minimal_spanning_tree pg vl el /\
      list_to_set s.(vertex_taken) ⊆ list_to_set vl /\
      list_to_set s.(edge_taken) ⊆ list_to_set el) /\
  subgraph {|
    vertices := s.(vertex_taken);
    edges := s.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |} pg)
  (add_the_edge_and_the_vertex pg e v)
  (fun _ s => exists (vl' : list V) (el' : list E),
  is_minimal_spanning_tree pg vl' el' /\
  list_to_set s.(vertex_taken) ⊆ list_to_set vl' /\
   list_to_set s.(edge_taken) ⊆ list_to_set el' /\ 
  subgraph {|
    vertices := s.(vertex_taken);
    edges := s.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
   |} pg).
Proof.
  intros.
  unfold Hoare, add_the_edge_and_the_vertex.
  intros; clear a.
  destruct H0 as [H2 [H3 [H4 [[vl [el [H5 [H6 H7]]]] L]]]].
  destruct H1 as [H0 H1].
  pose proof (intermediate_point_between_x_and_y pg σ1 e v vl el H H2 H3 H4 H5 H6 H7).
  destruct H8 as [f [x [? [? [? [? [? ?]]]]]]].
  pose proof (graph_after_delete_exists pg vl el f H5 H9).
  destruct
  H14 as [vl' [el' ?]].
  specialize (H13 vl' el' H14).
  exists vl', (e :: el').
  destruct H5.
  unfold is_spanning_tree in H5.
  destruct H5.
  assert (subgraph {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |} pg).
  { apply (keep_chosen_graph_subgraph pg σ1 σ2 e v H H3 H2 H0 H1 L).
  }
  split; [ tauto | split].
  + unfold is_graph_after_delete in H14.
    unfold is_new_list_delete_one_from_original in H14.
    unfold is_minimal_spanning_tree in H5.
    destruct H14.
    subst vl'.
    rewrite H0, H16.
    unfold list_to_set.
    sets_unfold.
    intros.
    destruct H18; [subst a | ].
    * unfold is_legal_graph in H17.
      destruct H17 as [_ [_ H17]].
      destruct H3 as [[? ?] _].
      destruct H as [[_ [_ H]] _].
      specialize (H e H3).
      destruct H2.
      destruct H2.
      subst v.
      tauto.
      destruct H2.
      subst v.
      tauto.
    * destruct L as [_ [_ _]].
      sets_unfold in subgraph_vvalid0.
      specialize (subgraph_vvalid0 a H18);tauto.
  + split; [ | tauto].
    unfold list_to_set.
    sets_unfold.
    intros e0 ?.
    rewrite H1 in H18.
    destruct H18; [subst; simpl; tauto | simpl; right].
    unfold is_graph_after_delete in H14.
    unfold is_new_list_delete_one_from_original in H14.
    destruct H14 as [H14 _].
    apply (H14 e0).
    split.
    ** unfold list_to_set in H7; sets_unfold in H7.
      apply (H7 e0 H18).
    ** destruct (classic (e0 = f)); [ subst; tauto | tauto].
Qed.

(* Level 3 *)
Theorem keep_I1 {V E: Type}:
  forall (pg: PreGraph V E),
        graph_connected pg -> 
        Hoare (fun s => I1 pg s /\ subgraph {|
          vertices := s.(vertex_taken);
          edges := s.(edge_taken);
          src := pg.(src);
          dst := pg.(dst);
          weight := pg.(weight)
        |} pg )
        (body_prim pg tt)
        (fun res (s: State V E) => 
            match res with
            | by_continue _ => I1 pg s /\ subgraph {|
              vertices := s.(vertex_taken);
              edges := s.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight) |} pg
            | by_break _ => I1 pg s /\ subgraph {|
              vertices := s.(vertex_taken);
              edges := s.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight) |} pg
            end).
Proof.
  intros.
  unfold I1.
  apply Hoare_choice.
  + apply Hoare_test_bind.
    intros.
    apply Hoare_ret'.
    intros.
    tauto.
  + apply Hoare_test_bind.
    eapply Hoare_bind.
    * apply (Hoare_get_any_edge_in_edge_candidates pg _).
    * intros e.
      eapply Hoare_bind.
      ++ apply (Hoare_get_any_vertex_in_vertex_candidates pg e _).
      ++ intros v.
          eapply Hoare_bind; [ | intros; apply Hoare_ret'].
          +++ apply (Hoare_add_the_edge_and_the_vertex_for_ismst pg e v).
              tauto.
          +++ intros.
              simpl in H0.
              destruct H0 as [vl [el ?]].
              split; [ | tauto].
              exists vl, el.
              tauto.
Qed.

(* Level 3 *)
Theorem break_with_I1 {V E: Type}:
  forall (pg: PreGraph V E),
  graph_connected pg -> 
  Hoare (fun s0 => I1 pg s0 /\ subgraph {|
    vertices := s0.(vertex_taken);
    edges := s0.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight) |} pg)
        (prim pg tt)
        (fun (_: unit) (s: State V E) => 
        I1 pg s /\ subgraph {|
          vertices := s.(vertex_taken);
          edges := s.(edge_taken);
          src := pg.(src);
          dst := pg.(dst);
          weight := pg.(weight) |} pg).
Proof.
  intros.
  unfold prim.
  apply (Hoare_repeat_break (body_prim pg) 
                            (fun (_: unit) (s0: State V E) => I1 pg s0 /\ subgraph {|
                              vertices := s0.(vertex_taken);
                              edges := s0.(edge_taken);
                              src := pg.(src);
                              dst := pg.(dst);
                              weight := pg.(weight) |} pg)
                            (fun (_: unit) (s: State V E) => 
                              I1 pg s /\ subgraph {|
                              vertices := s.(vertex_taken);
                              edges := s.(edge_taken);
                              src := pg.(src);
                              dst := pg.(dst);
                              weight := pg.(weight) |} pg)).
  intros.
  apply (keep_I1 pg).
  apply H.
Qed.

(* *************************************************************************** *)
(* 关于初始状态的命题 *)
(* Level 3 *)
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
    destruct (classic (A a)).
    - destruct (classic (exists a': Z, A a' /\ a' <> a)).
      * specialize (IHL (fun x => A x /\ x <> a)).
        Admitted.
        
      
(* Level 3 *)
Theorem finite_graph_has_finite_subgraphs {V E: Type}: 
  forall (pg: PreGraph V E), 
    exists subgl: list (PreGraph V E), (forall subg, In subg subgl <-> subgraph subg pg).
Proof.
  (* by induction *)
  Admitted.

(* Level 3*)
Theorem spanning_tree_exists {V E: Type}:
  forall (pg: PreGraph V E), 
    graph_connected pg -> 
    exists vl el, is_spanning_tree pg vl el.
Proof.
  (* by induction. *)
  Admitted.

(* Level 3 *)
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

(* Level 3 *)
Lemma initial_state {V E: Type} (s: State V E):
    forall (u: V) (pg: PreGraph V E),
    pg.(vvalid) u ->
    graph_connected pg -> 
    s.(vertex_taken) = u :: nil /\ s.(edge_taken) = nil -> I1 pg s /\ 
    subgraph {|
      vertices := s.(vertex_taken);
      edges := s.(edge_taken);
      src := pg.(src);
      dst := pg.(dst);
      weight := pg.(weight)
    |} pg.
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
Admitted.
(* ******************************************************************************* *)

(* Level 3 *)
Lemma no_dup_list_have_same_length_if_set_equal {V : Type}:
  forall (l1 l2: list V),
    NoDup l1 -> NoDup l2 -> 
    list_to_set l1 == list_to_set l2 -> 
    length l1 = length l2.
Proof.
intros l1.
induction l1.
+ intros.
  unfold list_to_set in H1.
  assert (H_eq: forall v', In v' [] <-> In v' l2).
  {
    intros.
    specialize (H1 v'). 
    assumption.
  }
  destruct l2.
  - reflexivity.
  - exfalso. specialize (H_eq v). simpl in H_eq. tauto.
+
  intros.
  assert (NoDup l1).
  {
    inversion H; tauto.
  }
  assert (In a l2).
  {
    unfold list_to_set in H1.
    sets_unfold in H1. 
    pose proof (H1 a).
    destruct H3.
    assert (In a (a :: l1)).
    {
      simpl; tauto.
    }
    pose proof (H3 H5).
    tauto.
  }
  pose proof (deleted_list_exists l2 a H0 H3).
  destruct H4 as [l2' ?].
  unfold is_new_list_delete_one_from_original in H4.
  destruct H4.
  destruct H5.
  rewrite <- H4.
  assert (length l1 = length l2').
  {
    pose proof (IHl1 l2' H2 H5).
    assert (list_to_set l1 == list_to_set l2').
    {
      split; intros.
      +  pose proof H6 a0.
          destruct H9.
          assert (list_to_set l2 a0).
          {
            unfold list_to_set in H1.
            sets_unfold in H1.
            pose proof (H1 a0).
            unfold list_to_set in H8.
            destruct H11.
            assert (In a0 (a :: l1)).
            {
              simpl; tauto.
            }
            pose proof (H11 H13).
            tauto.
          }
          unfold list_to_set in H11.
          assert (a0 <> a).
          {
            unfold list_to_set in H8.
            unfold list_to_set in H1.
            sets_unfold in H1.
            assert (~ In a l1).
            {
              inversion H; tauto.
            }
            destruct (classic (a0 = a)).
            + rewrite <- H13 in H12.
              tauto.
            + tauto.
          }
          assert (In a0 l2 /\ a0 <> a).
          {
            tauto.
          }
          pose proof (H10 H13).
          tauto.
      + pose proof H6 a0.
        destruct H9.
        unfold list_to_set in H8.
        pose proof (H9 H8).
        destruct H11.
        unfold list_to_set in H1.
        sets_unfold in H1.
        pose proof (H1 a0).
        destruct H13.
        pose proof (H14 H11).
        simpl in H15.
        destruct H15.
        ++ subst; tauto.
        ++ tauto.
    }
  pose proof (H7 H8).  
  tauto.
  }
  rewrite <- H7.
  simpl.
  lia.
Qed.

Lemma no_dup_set_equal_if_length_equal_and_set_include {V: Type}:
  forall (l1 l2: list V),
    length l1 = length l2 -> 
    list_to_set l1 ⊆ list_to_set l2 -> 
    NoDup l1 -> NoDup l2 -> 
    list_to_set l1 == list_to_set l2.
Proof.
    intros l1.
    induction l1.
    + intros.
      destruct l2.
      ++  reflexivity.
      ++ simpl in H.
          inversion H.
    + intros.
      assert (NoDup l1).
      {
        inversion H1; tauto.
      }
      unfold list_to_set in H0.
      sets_unfold in H0.
      assert (In a l2).
      {
        specialize (H0 a).
        assert (In a (a :: l1)).
        {
          simpl; tauto.
        }
        pose proof (H0 H4).
        tauto.
      }
      pose proof (deleted_list_exists l2 a H2 H4).
      destruct H5 as [l2' ?].
      destruct H5.
      destruct H6.
      unfold is_new_list_delete_one_from_original in H7.
      assert (list_to_set l1 ⊆ list_to_set l2').
      {
        unfold list_to_set.
        sets_unfold.
        intros.
        specialize (H7 a0).
        destruct H7.
        assert (a0 <> a).
        {
          assert (~ In a l1). 
          {
            inversion H1; tauto. 
          }
          destruct (classic (a0 = a)).
          + rewrite <- H11 in H10.
            tauto.
          + tauto.
        }
        assert (In a0 l2).
        {
          pose proof (H0 a0).
          assert (In a0 (a :: l1)).
          {
            simpl; tauto.
          }
          pose proof (H11 H12).
          tauto.
        }
        assert (In a0 l2 /\ a0 <> a).
        {
          tauto.
        }
        pose proof (H9 H12).
        tauto.
      }
      assert (length l1 + 1 = length l2' + 1).
      {
        rewrite H5.
        simpl in H.
        lia.
      }
      assert (length l1 = length l2').
      {
        lia.
      }
      pose proof (IHl1 l2' H10 H8 H3 H6).
      unfold list_to_set.
      sets_unfold.
      intros.
      destruct (classic (a0 = a)).
      ++ rewrite H12.
         split.
         -- intros.
            subst; tauto.
         -- intros.
            simpl.
            left.
            reflexivity.
      ++
        split. 
        --
          intros.
          assert (In a0 l1).
          {
            destruct H13.
            +++ subst; tauto.
            +++ tauto.
          }
          unfold list_to_set in H11.
          sets_unfold in H11.
          pose proof (H11 a0).
          destruct H15.
          pose proof (H15 H14).
          pose proof H7 a0.
          destruct H18.
          pose proof H18 H17.
          destruct H20.
          tauto.
        --
          intros.
          pose proof (H7 a0).
          destruct H14.
          assert (In a0 l2 /\ a0 <> a).
          {
            tauto.
          }
          pose proof (H15 H16).
          unfold list_to_set in H11.
          sets_unfold in H11.
          pose proof (H11 a0).
          destruct H18.
          pose proof (H19 H17).
          simpl.
          right.
          tauto.
  Qed.


Lemma get_sum_1n {V E: Type}:
  forall (pg: PreGraph V E) (l: list E) (e: E),
    get_sum pg (e :: l) = Z.add (get_sum pg l) (pg.(weight) e).
Proof.
  intros.
  unfold get_sum.
  assert ((e::l) = [e] ++ l).
  {
    simpl.
    reflexivity.
  }
  rewrite H.
  pose proof (fold_right_app Z.add [pg.(weight) e] (map pg.(weight) l) 0%Z).
  assert ([pg.(weight) e] ++ map pg.(weight) l = map pg.(weight) ([e] ++ l)).
  {
    simpl.
    reflexivity.
  }
  rewrite H1 in H0.
  rewrite H0.
  simpl.
  lia.
Qed.

Lemma no_dup_list_have_same_sum_if_set_equal {V E: Type}:
  forall (pg: PreGraph V E) (l1 l2: list E),
    NoDup l1 -> NoDup l2 -> 
    length l1 = length l2 ->
    list_to_set l1 == list_to_set l2 ->
    get_sum pg l1 = get_sum pg l2.
Proof.
  induction l1.
  + intros.
    assert (l2 = nil).
    {
      apply length_zero_iff_nil.
      rewrite <- H1.
      simpl.
      reflexivity.
    }
    rewrite H3.
    reflexivity.
  + intros.
    unfold list_to_set in H2.
    sets_unfold in H2.
    assert (In a (a::l1)).
    {
      simpl.
      tauto.
    }
    rewrite H2 in H3.
    pose proof (deleted_list_exists_with_sum_equal pg l2 a).
    pose proof H4 H0 H3.
    clear H4.
    destruct H5 as [l2' ?].
    destruct H4 as [X ?].
    unfold is_new_list_delete_one_from_original in H4.
    destruct H4.
    assert (NoDup l1).
    {
      inversion H.
      tauto.
    }
    assert (length l1 + 1 = length (a :: l1)).
    {
      simpl.
      lia.
    }
    rewrite H1 in H7.
    rewrite <- H4 in H7.
    assert (length l1 = length l2').
    {
      lia.
    }
    clear H7.
    destruct H5.
    assert (list_to_set l1 == list_to_set l2').
    {
      unfold list_to_set.
      sets_unfold.
      intros.
      split.
      + intros.
        assert (In a0 (a :: l1)).
        {
          simpl.
          right.
          tauto.
        }
        specialize (H2 a0).
        rewrite H2 in H10.
        destruct (classic (a0 = a)).
        - subst.
          apply NoDup_cons_iff in H.
          destruct H.
          tauto.
        - specialize (H7 a0).
          tauto.
      + intros.
        specialize (H7 a0).
        rewrite H7 in H9.
        destruct H9.
        specialize (H2 a0).
        rewrite <- H2 in H9.
        simpl in H9.
        destruct H9.
        ++ subst.
           tauto.
        ++ tauto. 
    }
    specialize (IHl1 l2' H6 H5 H8 H9).
    rewrite <- X.
    pose proof (get_sum_1n pg l1 a).
    rewrite H10.
    rewrite IHl1.
    reflexivity.
Qed.
    

(* Level 3 *)
Lemma I1_plus_I2_plus_I3_to_minimum_spanning_tree {V E: Type} (s: State V E):
  forall (pg: PreGraph V E),
    graph_connected pg -> 
    I1 pg s -> I2 pg s -> I3 pg s -> is_minimal_spanning_tree pg s.(vertex_taken) s.(edge_taken).
Proof.
  intros.
  unfold I1 in H0.
  unfold I3 in H0.
  destruct H0.
  destruct H0.
  unfold I2 in H1.
  unfold I3 in H2.
  destruct H0.
  destruct H3.
  pose proof H0.
  pose proof H1.
  unfold is_tree in H1.
  destruct H1.
  unfold graph_connected in H,H7.
  destruct H7.
  clear H8.
  destruct H.
  clear H8.
  unfold is_legal_graph in H.
  unfold is_minimal_spanning_tree in H0.
  destruct H0.
  unfold is_spanning_tree in H0.
  destruct H0.
  rewrite <- H2 in H9.
  unfold is_minimal_spanning_tree.
  split.
  + split; auto.
  + intros.
    specialize (H8 vl' el').
    clear H3.
    unfold is_tree in H0.
    destruct H0.
    unfold graph_connected in H3.
    destruct H3.
    clear H11.
    unfold is_legal_graph in H3.
    destruct H3.
    destruct H11.
    clear H12.
    simpl in H3, H11.
    unfold is_legal_graph in H7.
    destruct H7.
    destruct H12.
    clear H13.
    simpl in H7, H12.
    pose proof (no_dup_list_have_same_length_if_set_equal x s.(vertex_taken)).
    pose proof H13 H3 H7 H9.
    clear H13.
    rewrite H14 in H0.
    rewrite <- H1 in H0.
    assert (length x0 = length s.(edge_taken)).
    {
      lia.
    }
    clear H14.
    clear H7.
    clear H1.
    clear H0.
    clear H9.
    clear H3.
    clear H2.
    pose proof (no_dup_set_equal_if_length_equal_and_set_include s.(edge_taken) x0).
    assert (length s.(edge_taken) = length x0).
    {
      lia.
    }
    pose proof H0 H1 H4 H12 H11.
    clear H0 H13.
    pose proof (no_dup_list_have_same_sum_if_set_equal pg s.(edge_taken) x0).
    pose proof H0 H12 H11 H1 H2.
    rewrite H3.
    pose proof H8 H10.
    tauto.
Qed.


Theorem prim_functional_correctness_foundation {V E: Type}: 
    forall (u: V) (pg: PreGraph V E),
        pg.(vvalid) u ->
        graph_connected pg -> 
        Hoare (fun s => I1 pg s /\ I2 pg s /\ subgraph {|
          vertices := s.(vertex_taken);
          edges := s.(edge_taken);
          src := pg.(src);
          dst := pg.(dst);
          weight := pg.(weight)
        |} pg)
              (prim pg tt)
              (fun (_: unit) (s: State V E) => 
              is_minimal_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
  intros.
  pose proof (prim_find_tree_if_break_f pg).
  pose proof (prim_find_all_vertices_if_break_f pg).
  pose proof (break_with_I1 pg).
  pose proof H1 H0.
  clear H1.
  pose proof H2 H0.
  clear H2.
  pose proof H3 H0.
  clear H3.
  unfold Hoare in H1, H2, H4.
  unfold Hoare.
  intros.
  specialize (H1 σ1 a σ2).
  specialize (H2 σ1 a σ2).
  specialize (H4 σ1 a σ2).
  destruct H3 as [? [? ?]].
  pose proof H4 H6 H5.
  pose proof H1 H6 H5.
  assert (I1 pg σ1 /\
  subgraph
    {|
      vertices := σ1.(vertex_taken);
      edges := σ1.(edge_taken);
      src := pg.(src);
      dst := pg.(dst);
      weight := pg.(weight)
    |} pg).
  {
    split;auto.
  }
  pose proof H2 H10 H5.
  pose proof (I1_plus_I2_plus_I3_to_minimum_spanning_tree σ2 pg).
  destruct H11.
  pose proof H12 H0 H11 H8 H9.
  tauto.
Qed.


Theorem prim_functional_correctness {V E: Type}:
    forall (u: V) (pg: PreGraph V E),
      pg.(vvalid) u ->
      graph_connected pg -> 
      Hoare (fun s0 => s0.(vertex_taken) = u :: nil /\ s0.(edge_taken) = nil)
            (prim pg tt)
            (fun (_: unit) (s: State V E) => 
                is_minimal_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
  intros.
  unfold Hoare.
  intros.
  pose proof (prim_functional_correctness_foundation u pg).
  pose proof (initial_state σ1 u pg).
  pose proof (initial_state_to_I2 σ1 u pg).
  pose proof H3 H H0.
  clear H3.
  pose proof H4 H H0 H1.
  clear H4.
  pose proof H5 H H0 H1.
  clear H5.
  unfold Hoare in H6.
  destruct H3.
  specialize (H6 σ1 a σ2).
  destruct H6.
  + split;[tauto|split;[tauto|tauto]].
  + tauto.
  + unfold is_minimal_spanning_tree.
    split; auto.
Qed.
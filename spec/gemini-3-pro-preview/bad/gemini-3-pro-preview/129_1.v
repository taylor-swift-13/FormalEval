Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Helper function to access grid values safely *)
Definition get_grid_val (grid : list (list Z)) (r c : Z) : option Z :=
  match nth_error grid (Z.to_nat r) with
  | Some row => nth_error row (Z.to_nat c)
  | None => None
  end.

(* Predicate for valid grid bounds *)
Definition in_bounds (N : Z) (r c : Z) : Prop :=
  0 <= r < N /\ 0 <= c < N.

(* Predicate for grid adjacency (Manhattan distance of 1) *)
Definition is_adjacent (r1 c1 r2 c2 : Z) : Prop :=
  Z.abs (r1 - r2) + Z.abs (c1 - c2) = 1.

(* Inductive predicate to define a valid path of coordinates in the grid *)
Inductive valid_path_coords (N : Z) : list (Z * Z) -> Prop :=
| vp_start : forall r c, 
    in_bounds N r c -> 
    valid_path_coords N [(r, c)]
| vp_step : forall r1 c1 r2 c2 rest,
    in_bounds N r1 c1 ->
    is_adjacent r1 c1 r2 c2 ->
    valid_path_coords N ((r2, c2) :: rest) ->
    valid_path_coords N ((r1, c1) :: (r2, c2) :: rest).

(* Function to map a list of coordinates to their values in the grid *)
Fixpoint map_coords_to_values (grid : list (list Z)) (coords : list (Z * Z)) : list Z :=
  match coords with
  | [] => []
  | (r, c) :: rest =>
      match get_grid_val grid r c with
      | Some v => v :: map_coords_to_values grid rest
      | None => [] (* Should not happen for valid paths *)
      end
  end.

(* Inductive predicate for lexicographical less-than-or-equal comparison *)
Inductive lex_le : list Z -> list Z -> Prop :=
| lex_nil : forall l, lex_le [] l
| lex_cons_lt : forall x y xs ys, 
    x < y -> 
    lex_le (x :: xs) (y :: ys)
| lex_cons_eq : forall x xs ys, 
    lex_le xs ys -> 
    lex_le (x :: xs) (x :: ys).

(* Main Specification *)
Definition minPath_spec (grid : list (list Z)) (k : Z) (result : list Z) : Prop :=
  let N := Z.of_nat (length grid) in
  (* Preconditions *)
  N >= 2 /\
  k > 0 /\
  (forall row, In row grid -> length row = Z.to_nat N) /\
  (* Every integer in [1, N*N] appears exactly once (implied permutation property) *)
  (forall z, 1 <= z <= N * N -> 
     exists r c, in_bounds N r c /\ get_grid_val grid r c = Some z) /\
  
  (* Postconditions *)
  length result = Z.to_nat k /\
  
  (* 1. The result corresponds to a valid path in the grid *)
  (exists coords, 
     length coords = Z.to_nat k /\
     valid_path_coords N coords /\
     map_coords_to_values grid coords = result) /\
     
  (* 2. The result is lexicographically minimal among all valid paths of length k *)
  (forall other_coords other_vals,
     length other_coords = Z.to_nat k ->
     valid_path_coords N other_coords ->
     map_coords_to_values grid other_coords = other_vals ->
     lex_le result other_vals).

(* Test Case Definitions *)
Definition test_grid : list (list Z) := 
  [[1; 2; 3]; [4; 5; 6]; [7; 8; 9]].
Definition test_k : Z := 3.
Definition test_res : list Z := [1; 2; 1].

(* Proof of the test case *)
Example test_minPath : minPath_spec test_grid test_k test_res.
Proof.
  unfold minPath_spec.
  simpl.
  
  repeat split.
  - (* N >= 2 *) lia.
  - (* k > 0 *) lia.
  - (* Row lengths *)
    intros row HIn.
    destruct HIn as [<- | [<- | [<- | []]]]; reflexivity.
  - (* Permutation property (1..9 exist in grid) *)
    intros z Hz.
    assert (Hz_cases: z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9) by lia.
    destruct Hz_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    [ exists 0, 0 | exists 0, 1 | exists 0, 2 | exists 1, 0 | exists 1, 1 | exists 1, 2 | exists 2, 0 | exists 2, 1 | exists 2, 2 ];
    split; try (unfold in_bounds; lia); simpl; reflexivity.

  - (* Result length check *)
    reflexivity.

  - (* Existence of the specific path [(0,0); (0,1); (0,0)] *)
    exists [(0, 0); (0, 1); (0, 0)].
    split; [reflexivity |].
    split.
    + (* Proof of valid_path_coords *)
      repeat constructor; unfold in_bounds, is_adjacent in *; simpl; try lia.
    + (* Proof of map_coords_to_values *)
      simpl. reflexivity.

  - (* Optimality Proof *)
    intros other_coords other_vals Hlen Hvalid Hmap.
    
    (* Deconstruct the path based on known length 3 *)
    destruct other_coords as [|p1 [|p2 [|p3 [|]]]]; simpl in Hlen; try lia.
    destruct p1 as [r1 c1], p2 as [r2 c2], p3 as [r3 c3].
    
    (* Invert validity to get bounds and adjacency info *)
    inversion Hvalid as [|? ? ? ? ? Hinv1 Hinv_adj1 Hinv_rest1]; subst.
    inversion Hinv_rest1 as [|? ? ? ? ? Hinv2 Hinv_adj2 Hinv_rest2]; subst.
    inversion Hinv_rest2 as [|? ? Hinv3]; subst.
    
    (* Helper tactic to enumerate coordinates *)
    Ltac enum_coords r c :=
      assert (r = 0 \/ r = 1 \/ r = 2) by lia;
      assert (c = 0 \/ c = 1 \/ c = 2) by lia.

    (* Evaluate map_coords_to_values *)
    simpl in Hmap.
    remember (get_grid_val test_grid r1 c1) as ov1.
    remember (get_grid_val test_grid r2 c2) as ov2.
    remember (get_grid_val test_grid r3 c3) as ov3.
    destruct ov1 as [v1|]; [|discriminate].
    destruct ov2 as [v2|]; [|discriminate].
    destruct ov3 as [v3|]; [|discriminate].
    injection Hmap as <- <- <-.

    (* --- Step 1: Compare v1 vs 1 --- *)
    (* Since v1 is in the grid, v1 >= 1. *)
    assert (Hv1_ge_1: v1 >= 1). {
       enum_coords r1 c1;
       destruct H2 as [-> | [-> | ->]]; destruct H3 as [-> | [-> | ->]];
       rewrite Heqov1 in *; simpl in *; injection Heqov1 as <-; lia.
    }
    
    destruct (Z_lt_dec 1 v1).
    { apply lex_cons_lt. assumption. }
    {
      assert (v1 = 1) by lia. subst v1.
      apply lex_cons_eq.
      
      (* v1 = 1 implies (r1, c1) = (0, 0) *)
      assert (Hr1c1: r1 = 0 /\ c1 = 0). {
         enum_coords r1 c1;
         destruct H2 as [-> | [-> | ->]]; destruct H3 as [-> | [-> | ->]];
         rewrite Heqov1 in *; simpl in *; try discriminate; injection Heqov1 as eq; try lia; auto.
      }
      destruct Hr1c1; subst r1 c1.
      
      (* --- Step 2: Compare v2 vs 2 --- *)
      (* Neighbors of (0,0) are (0,1)[2] and (1,0)[4]. So v2 >= 2. *)
      unfold is_adjacent in Hinv_adj1. simpl in Hinv_adj1.
      
      assert (v2 = 2 \/ v2 = 4). {
        enum_coords r2 c2;
        destruct H2 as [-> | [-> | ->]]; destruct H3 as [-> | [-> | ->]];
        simpl in Hinv_adj1; try lia;
        rewrite Heqov2 in *; simpl in *; injection Heqov2 as <-; auto.
      }
      
      destruct (Z_lt_dec 2 v2).
      { apply lex_cons_lt. assumption. }
      {
        assert (v2 = 2) by lia. subst v2.
        apply lex_cons_eq.
        
        (* v2 = 2 implies (r2, c2) = (0, 1) *)
        assert (Hr2c2: r2 = 0 /\ c2 = 1). {
           enum_coords r2 c2;
           destruct H2 as [-> | [-> | ->]]; destruct H3 as [-> | [-> | ->]];
           rewrite Heqov2 in *; simpl in *; try discriminate; injection Heqov2 as eq; try lia; auto.
        }
        destruct Hr2c2; subst r2 c2.
        
        (* --- Step 3: Compare v3 vs 1 --- *)
        (* Neighbors of (0,1) are (0,0)[1], (0,2)[3], (1,1)[5]. So v3 >= 1. *)
        unfold is_adjacent in Hinv_adj2. simpl in Hinv_adj2.
        
        assert (v3 = 1 \/ v3 = 3 \/ v3 = 5). {
           enum_coords r3 c3;
           destruct H2 as [-> | [-> | ->]]; destruct H3 as [-> | [-> | ->]];
           simpl in Hinv_adj2; try lia;
           rewrite Heqov3 in *; simpl in *; injection Heqov3 as <-; auto.
        }
        
        destruct (Z_lt_dec 1 v3).
        { apply lex_cons_lt. assumption. }
        {
           assert (v3 = 1) by lia. subst v3.
           apply lex_cons_eq.
           apply lex_nil.
        }
      }
    }
Qed.
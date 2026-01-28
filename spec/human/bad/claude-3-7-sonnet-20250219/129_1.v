Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Definition Grid := list (list nat).
Definition Pos := (nat * nat)%type.

Definition in_bounds (grid : Grid) (p : Pos) : bool :=
  let '(r,c) := p in
  andb (r <? length grid)
       (match nth_error grid r with
        | Some row => c <? length row
        | None => false
        end).

Definition neighbors (p:Pos) : list Pos :=
  let '(r,c) := p in [(r, c+1); (r+1, c); (r, c-1); (r-1, c)].

Fixpoint get_val (grid:Grid) (p:Pos) : nat :=
  let '(r,c) := p in
  match nth_error grid r with
  | Some row => match nth_error row c with Some v => v | None => 0 end
  | None => 0
  end.

Fixpoint lex_le (l1 l2 : list nat) : bool :=
  match l1,l2 with
  | [], _ => true
  | _::_, [] => false
  | h1::t1, h2::t2 => (h1 <? h2) || (andb (h1 =? h2) (lex_le t1 t2))
  end.

Fixpoint extend_paths (grid:Grid) (k:nat) (fuel:nat) (paths:list (list Pos)) : list (list Pos) :=
  match fuel with
  | 0 => paths
  | S f' =>
    if k <=? 1 then paths else
    let ex :=
      fold_right (fun p acc =>
        match p with
        | [] => acc | q::_ =>
          fold_right (fun nb acc2 => if in_bounds grid nb then (nb::p)::acc2 else acc2)
                     acc (neighbors q)
        end) [] paths in
    extend_paths grid (k-1) f' ex
  end.

Definition get_path_values (grid:Grid) (path:list Pos) : list nat := map (get_val grid) (rev path).

Fixpoint best_by_lex (grid:Grid) (candidates:list (list Pos)) : list nat :=
  match candidates with
  | [] => []
  | p::ps =>
    let v := get_path_values grid p in
    let best_rest := best_by_lex grid ps in
    if lex_le v best_rest then v else best_rest
  end.

Fixpoint build_row_starts (r:nat) (row:list nat) (c:nat) : list (list Pos) :=
  match row with
  | [] => []
  | _::t => [(r,c)] :: build_row_starts r t (S c)
  end.

Fixpoint build_starts (g:Grid) (r:nat) : list (list Pos) :=
  match g with
  | [] => []
  | row::gs => build_row_starts r row 0 ++ build_starts gs (S r)
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  let starts := build_starts grid 0 in
  let cand := extend_paths grid k (k * (length grid + 1)) starts in
  best_by_lex grid cand.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Definition example_grid : Grid := [[1;2;3]; [4;5;6]; [7;8;9]].
Definition example_k : nat := 3.
Definition example_output : list nat := [1;2;1].

Example problem_129_example :
  problem_129_spec example_grid example_k example_output.
Proof.
  unfold problem_129_spec, find_minimum_path_impl.
  (* unfold build_starts to get starting positions *)
  remember (build_starts example_grid 0) as starts eqn:Hstarts.
  assert (starts =
    [[(0,0)]; [(0,1)]; [(0,2)];
     [(1,0)]; [(1,1)]; [(1,2)];
     [(2,0)]; [(2,1)]; [(2,2)]])
    as Hstarts_eq.
  { subst starts. clear. reflexivity. }
  rewrite Hstarts_eq.
  clear Hstarts.

  (* Calculate fuel *)
  set (fuel := example_k * (length example_grid + 1)).
  unfold example_k, example_grid in fuel.
  simpl in fuel. (* fuel = 3 * (3+1) = 12 *)

  (* Let cand := extend_paths example_grid 3 12 (list of starts) *)
  remember (extend_paths example_grid 3 12
    [[(0,0)];[(0,1)];[(0,2)];
     [(1,0)];[(1,1)];[(1,2)];
     [(2,0)];[(2,1)];[(2,2)]]) as cand eqn:Hcand.

  (* best_by_lex selects minimal lex path values *)
  remember (best_by_lex example_grid cand) as best eqn:Hbest.

  (* According to specification and uniqueness, the minimal path values is [1;2;1] *)
  (* The implementation is deterministic and exhaustive, so equality should hold *)
  clear Heqstarts Hstarts_eq Heqcand.

  (* We do not want to fully unfold extend_paths due to complexity.
     Instead, rely on determinism and uniqueness statement in specification. *)

  subst best.
  subst cand.

  (* as a tactic: use vm_compute or native_compute, if your Coq environment supports it *)
  vm_compute.
  reflexivity.
Qed.
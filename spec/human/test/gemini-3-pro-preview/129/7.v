Require Import Coq.Lists.List Coq.Arith.Arith.
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
  let '(r,c) := p in
  [(r, c+1); (r+1, c)] ++ 
  (if Nat.eqb c 0 then [] else [(r, c-1)]) ++ 
  (if Nat.eqb r 0 then [] else [(r-1, c)]).

Fixpoint get_val (grid:Grid) (p:Pos) : nat :=
  let '(r,c) := p in
  match nth_error grid r with
  | Some row => match nth_error row c with Some v => v | None => 0 end
  | None => 0
  end.

Fixpoint pos_eqb (p1 p2 : Pos) : bool :=
  let '(r1, c1) := p1 in
  let '(r2, c2) := p2 in
  andb (r1 =? r2) (c1 =? c2).

Fixpoint member_pos (x : Pos) (l : list Pos) : bool :=
  match l with
  | [] => false
  | y::tl => if pos_eqb x y then true else member_pos x tl
  end.

Fixpoint dedup_pos_aux (l : list Pos) (acc : list Pos) : list Pos :=
  match l with
  | [] => rev acc
  | x::xs => if member_pos x acc then dedup_pos_aux xs acc else dedup_pos_aux xs (x::acc)
  end.

Definition dedup_pos (l : list Pos) := dedup_pos_aux l [].

Fixpoint min_nat_list_aux (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x::xs => min_nat_list_aux xs (min x acc)
  end.

Definition min_nat_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x::xs => min_nat_list_aux xs x
  end.

Fixpoint enumerate_cols (r:nat) (c:nat) (row:list nat) : list Pos :=
  match row with
  | [] => []
  | _::cs => (r,c) :: enumerate_cols r (S c) cs
  end.

Fixpoint enumerate_grid (r:nat) (g:Grid) : list Pos :=
  match g with
  | [] => []
  | row::rows => enumerate_cols r 0 row ++ enumerate_grid (S r) rows
  end.

Definition get_all_pos (g:Grid) : list Pos := enumerate_grid 0 g.

Definition filter_pos_by_val (g:Grid) (ps:list Pos) (v:nat) : list Pos :=
  filter (fun p => Nat.eqb (get_val g p) v) ps.

Definition step (g:Grid) (current_ps:list Pos) : (nat * list Pos) :=
  let candidates := flat_map neighbors current_ps in
  let valid := filter (in_bounds g) candidates in
  let vals := map (get_val g) valid in
  match vals with
  | [] => (0, [])
  | _ =>
    let min_v := min_nat_list vals in
    let next_ps := filter_pos_by_val g valid min_v in
    (min_v, dedup_pos next_ps)
  end.

Fixpoint loop_steps (g:Grid) (k:nat) (current_ps:list Pos) (acc:list nat) : list nat :=
  match k with
  | 0 => rev acc
  | S k' =>
    match current_ps with
    | [] => rev acc
    | _ =>
      let '(v, next_ps) := step g current_ps in
      loop_steps g k' next_ps (v :: acc)
    end
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  let all_ps := get_all_pos grid in
  let all_vals := map (get_val grid) all_ps in
  match all_vals with
  | [] => []
  | _ =>
    let min_v := min_nat_list all_vals in
    let start_ps := filter_pos_by_val grid all_ps min_v in
    if Nat.eqb k 0 then [] else
    min_v :: loop_steps grid (pred k) start_ps []
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[12; 13; 10; 1]; [9; 3; 15; 6]; [5; 16; 14; 4]; [11; 8; 7; 2]] in
  let k := 12 in
  let output := [1; 6; 1; 6; 1; 6; 1; 6; 1; 6; 1; 6] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.
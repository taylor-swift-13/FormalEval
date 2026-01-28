Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint remove_one (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if Z.eqb x h then t else h :: remove_one x t
  end.

Fixpoint list_min (l : list Z) : option Z :=
  match l with
  | [] => None
  | h :: t =>
    match list_min t with
    | None => Some h
    | Some m => Some (Z.min h m)
    end
  end.

Fixpoint list_max (l : list Z) : option Z :=
  match l with
  | [] => None
  | h :: t =>
    match list_max t with
    | None => Some h
    | Some m => Some (Z.max h m)
    end
  end.

Fixpoint strange_sort_aux (l : list Z) (fuel : nat) (is_min : bool) : list Z :=
  match fuel with
  | 0%nat => []
  | S n =>
    match l with
    | [] => []
    | _ =>
      match if is_min then list_min l else list_max l with
      | None => []
      | Some v => v :: strange_sort_aux (remove_one v l) n (negb is_min)
      end
    end
  end.

Definition strange_sort_list (l : list Z) : list Z :=
  strange_sort_aux l (length l) true.

Definition problem_70_pre (l_in : list Z) : Prop := True.

Definition problem_70_spec (l_in l_out : list Z) : Prop :=
  l_out = strange_sort_list l_in.

Example test_strange_sort_1 :
  problem_70_spec [1%Z; 2%Z; 3%Z; 4%Z] [1%Z; 4%Z; 2%Z; 3%Z].
Proof.
  unfold problem_70_spec, strange_sort_list.
  (* unfold strange_sort_aux with fuel = length [1;2;3;4] = 4, is_min = true *)
  unfold strange_sort_aux.
  simpl.
  (* list_min [1;2;3;4] = Some 1 *)
  replace (strange_sort_aux [1; 2; 3; 4] 4 true)
    with (1 :: strange_sort_aux (remove_one 1 [1;2;3;4]) 3 false).
  {
    simpl.
    (* Now strange_sort_aux [2;3;4] 3 false *)
    unfold strange_sort_aux.
    simpl.
    (* list_max [2;3;4] = Some 4 *)
    replace (strange_sort_aux [2;3;4] 3 false)
      with (4 :: strange_sort_aux (remove_one 4 [2;3;4]) 2 true).
    {
      simpl.
      (* strange_sort_aux [2;3] 2 true *)
      unfold strange_sort_aux.
      simpl.
      (* list_min [2;3] = Some 2 *)
      replace (strange_sort_aux [2;3] 2 true)
        with (2 :: strange_sort_aux (remove_one 2 [2;3]) 1 false).
      {
        simpl.
        (* strange_sort_aux [3] 1 false *)
        unfold strange_sort_aux.
        simpl.
        (* list_max [3] = Some 3 *)
        replace (list_max [3]) with (Some 3) by reflexivity.
        simpl.
        unfold remove_one.
        simpl.
        rewrite Z.eqb_refl.
        simpl.
        reflexivity.
      }
      {
        simpl.
        unfold remove_one.
        simpl.
        rewrite Z.eqb_refl.
        reflexivity.
      }
    }
    {
      simpl.
      unfold remove_one.
      simpl.
      rewrite Z.eqb_neq.
      - reflexivity.
      - discriminate.
    }
  }
  {
    simpl.
    unfold remove_one.
    simpl.
    rewrite Z.eqb_refl.
    reflexivity.
  }
Qed.
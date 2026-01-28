Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.

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

Example test_strange_sort_list :
  strange_sort_list [12%Z; -15%Z; 81%Z; 82%Z; 5%Z; 14%Z; 80%Z; 20%Z; 25%Z; 82%Z] = [-15%Z; 82%Z; 5%Z; 82%Z; 12%Z; 81%Z; 14%Z; 80%Z; 20%Z; 25%Z].
Proof.
  unfold strange_sort_list.
  simpl.
  reflexivity.
Qed.
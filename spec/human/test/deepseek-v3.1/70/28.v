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

Lemma remove_one_test : remove_one 1%Z [1%Z; 2%Z; 3%Z; 4%Z] = [2%Z; 3%Z; 4%Z].
Proof. reflexivity. Qed.

Lemma list_min_test : list_min [1%Z; 2%Z; 3%Z; 4%Z] = Some 1%Z.
Proof. reflexivity. Qed.

Lemma list_max_test : list_max [2%Z; 3%Z; 4%Z] = Some 4%Z.
Proof. reflexivity. Qed.

Lemma remove_one_test2 : remove_one 4%Z [2%Z; 3%Z; 4%Z] = [2%Z; 3%Z].
Proof. reflexivity. Qed.

Lemma list_min_test2 : list_min [2%Z; 3%Z] = Some 2%Z.
Proof. reflexivity. Qed.

Lemma list_max_test2 : list_max [3%Z] = Some 3%Z.
Proof. reflexivity. Qed.

Lemma remove_one_test3 : remove_one 2%Z [2%Z; 3%Z] = [3%Z].
Proof. reflexivity. Qed.

Lemma remove_one_test4 : remove_one 3%Z [3%Z] = [].
Proof. reflexivity. Qed.

Example test_strange_sort_zero: strange_sort_list [0%Z] = [0%Z].
Proof.
  unfold strange_sort_list.
  simpl.
  reflexivity.
Qed.
(* 引入 Coq 标准库以使用列表、自然数和置换等概念 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.

(* 引入列表的标准表示法，如 [] 和 x :: xs *)
Import ListNotations.
Open Scope Z_scope.

(* Definitions provided in the specification *)

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

(* Test case proof *)

Example test_strange_sort_complex : problem_70_spec [-1; 0; -3; 5; 3; 4; 2; 60; 10; 7] [-3; 60; -1; 10; 0; 7; 2; 5; 3; 4].
Proof.
  (* Unfold the specification definition *)
  unfold problem_70_spec.
  
  (* Unfold the function definition *)
  unfold strange_sort_list.
  
  (* 
     Since all inputs are concrete values (integers and finite lists), 
     we can simply compute the result of the function and check if it matches the expected output.
     reflexivity automatically performs simplification and checks for equality.
  *)
  reflexivity.
Qed.
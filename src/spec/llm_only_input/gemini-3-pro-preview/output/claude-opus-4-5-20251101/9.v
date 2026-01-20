Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

(* Specification Definitions *)

Fixpoint max_list (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | x :: xs => Z.max x (max_list xs x)
  end.

Fixpoint firstn {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | x :: xs => x :: firstn n' xs
            end
  end.

Fixpoint rolling_max_aux (numbers : list Z) (idx : nat) : list Z :=
  match idx with
  | O => []
  | S n => rolling_max_aux numbers n ++ [max_list (firstn idx numbers) 0]
  end.

Definition rolling_max (numbers : list Z) : list Z :=
  rolling_max_aux numbers (length numbers).

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length result = length numbers /\
  forall i : nat, (i < length numbers)%nat ->
    nth i result 0 = max_list (firstn (S i) numbers) 0.

(* Test Case Proof *)

Example test_rolling_max_empty : rolling_max [] = [].
Proof.
  (* Unfold the definition of rolling_max to expose rolling_max_aux *)
  unfold rolling_max.
  
  (* Simplify the expression. 
     length [] reduces to 0.
     rolling_max_aux [] 0 reduces to []. *)
  simpl.
  
  (* The goal becomes [] = [], which is true by reflexivity *)
  reflexivity.
Qed.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition interp_op (op : ascii) : (Z -> Z -> Z) :=
  match op with
  | "+"%char => Z.add
  | "-"%char => Z.sub
  | "*"%char => Z.mul
  | "/"%char => Z.div
  | "^"%char => Z.pow
  | _ => fun _ _ => 0
  end.

Fixpoint find_index_aux {A} (p : A -> bool) (l : list A) (n : nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if p x then Some n else find_index_aux p xs (S n)
  end.

Definition find_index {A} (p : A -> bool) (l : list A) : option nat :=
  find_index_aux p l 0.

Definition rfind_index {A} (p : A -> bool) (l : list A) : option nat :=
  match find_index p (rev l) with
  | Some i => Some ((length l - 1) - i)%nat
  | None => None
  end.

Fixpoint eval_helper (ops : list ascii) (nums : list Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
    match nums with
    | [] => 0
    | [n] => n
    | _ :: _ =>
      match rfind_index (fun c => orb (c =? "+"%char)%char (c =? "-"%char)%char) ops with
      | Some i =>
          let op := nth i ops (" "%char) in
          interp_op op
            (eval_helper (firstn i ops) (firstn (i + 1) nums) fuel')
            (eval_helper (skipn (i + 1) ops) (skipn (i + 1) nums) fuel')
      | None =>
          match rfind_index (fun c => orb (c =? "*"%char)%char (c =? "/"%char)%char) ops with
          | Some i =>
              let op := nth i ops (" "%char) in
              interp_op op
                (eval_helper (firstn i ops) (firstn (i + 1) nums) fuel')
                (eval_helper (skipn (i + 1) ops) (skipn (i + 1) nums) fuel')
          | None =>
              match find_index (fun c => (c =? "^"%char)%char) ops with
              | Some i =>
                  let op := nth i ops (" "%char) in
                  interp_op op
                    (eval_helper (firstn i ops) (firstn (i + 1) nums) fuel')
                    (eval_helper (skipn (i + 1) ops) (skipn (i + 1) nums) fuel')
              | None => 0
              end
          end
      end
    end
  end.

Definition eval (ops : list ascii) (nums : list Z) : Z :=
  eval_helper ops nums (length nums).

Definition do_algebra_impl (operators : string) (operands : list Z) : Z :=
  eval (list_ascii_of_string operators) operands.

Example do_algebra_example :
  do_algebra_impl "^*+" [2%Z; 3%Z; 4%Z; 5%Z] = 37%Z.
Proof.
  unfold do_algebra_impl, eval.
  (* list_ascii_of_string "^*+" = ['^'; '*'; '+'] *)
  remember ("^*+"%string) as s eqn:Hs.
  assert (list_ascii_of_string s = ["^"%char; "*"%char; "+"%char]) as Hops.
  { subst s. reflexivity. }
  rewrite Hops; clear Hops.
  remember [2%Z; 3%Z; 4%Z; 5%Z] as nums eqn:Hnums.

  (* fuel = 4 *)
  (* Step 1: eval_helper ["^"; "*"; "+"] [2;3;4;5] 4 *)

  (* rfind_index '+' or '-' in ops *)
  (* rev ops = ['+'; '*'; '^'] *)
  (* find_index finds '+' at index 0 *)
  (* so rfind_index returns (3 - 1 - 0) = 2 *)
  assert (rfind_index (fun c => orb (c =? "+"%char)%char (c =? "-"%char)%char) ["^"%char; "*"%char; "+"%char] = Some 2).
  {
    unfold rfind_index, find_index, find_index_aux.
    simpl.
    (* Rev = ["+"; "*"; "^"] *)
    (* p '+' = true *)
    reflexivity.
  } 
  rewrite H at 1.
  clear H.

  remember 2 as i eqn:Hi.
  assert (nth i ["^"%char; "*"%char; "+"%char] " "%char = "+"%char).
  { subst i; simpl; reflexivity. }
  rewrite H.

  (* Split computation: eval_helper (firstn 2 ops) (firstn 3 operands) 3 and eval_helper (skipn 3 ops) (skipn 3 operands) 3 *)
  (* firstn 2 ops = ["^"; "*"] *)
  (* firstn 3 nums = [2; 3; 4] *)
  (* skipn 3 ops = [] *)
  (* skipn 3 nums = [5] *)

  assert (eval_helper [] [5] 3 = 5).
  { simpl; reflexivity. }
  rewrite H.
  clear H.

  (* Now compute eval_helper ["^"; "*"] [2;3;4] 3 *)

  (* Check rfind_index '+' or '-' *)
  assert (rfind_index (fun c => orb (c =? "+"%char)%char (c =? "-"%char)%char) ["^"%char; "*"%char] = None).
  {
    unfold rfind_index, find_index, find_index_aux.
    simpl.
    (* rev ops = ["*"; "^"], none '+/-' *)
    reflexivity.
  }

  (* Check rfind_index '*' or '/' *)
  assert (rfind_index (fun c => orb (c =? "*"%char)%char (c =? "/"%char)%char) ["^"%char; "*"%char] = Some 1).
  {
    unfold rfind_index, find_index, find_index_aux.
    simpl.
    (* rev ops = ["*"; "^"], '*' at index 0 *)
    reflexivity.
  }
  rewrite H.

  remember 1 as j eqn: Hj.
  assert (nth j ["^"%char; "*"%char] " "%char = "*"%char).
  { subst j; simpl; reflexivity. }
  rewrite H.

  (* Split further: eval_helper (firstn 1 ops) (firstn 2 nums) 2 and eval_helper (skipn 2 ops) (skipn 2 nums) 2 *)
  (* firstn 1 ops = ["^"] *)
  (* firstn 2 nums = [2; 3] *)
  (* skipn 2 ops = [] *)
  (* skipn 2 nums = [4] *)

  assert (eval_helper [] [4] 2 = 4).
  { simpl; reflexivity. }
  rewrite H.
  clear H.

  (* Compute eval_helper ["^"] [2;3] 2 *)

  (* Check rfind_index '+' or '-' *)
  assert (rfind_index (fun c => orb (c =? "+"%char)%char (c =? "-"%char)%char) ["^"%char] = None).
  {
    unfold rfind_index, find_index, find_index_aux.
    simpl.
    (* rev = ["^"], no '+' or '-' *)
    reflexivity.
  }

  (* Check rfind_index '*' or '/' *)
  assert (rfind_index (fun c => orb (c =? "*"%char)%char (c =? "/"%char)%char) ["^"%char] = None).
  {
    unfold rfind_index, find_index, find_index_aux.
    simpl.
    reflexivity.
  } 

  (* Check find_index '^' *)
  assert (find_index (fun c => (c =? "^"%char)%char) ["^"%char] = Some 0).
  {
    unfold find_index, find_index_aux.
    simpl.
    reflexivity.
  }
  rewrite H.

  remember 0 as k eqn:Hk.
  assert (nth k ["^"%char] " "%char = "^"%char).
  { subst k; simpl; reflexivity. }
  rewrite H.

  (* Split eval_helper (firstn 0 ops) (firstn 1 nums) 1 and eval_helper (skipn 1 ops) (skipn 1 nums) 1 *)
  (* firstn 0 ops = [] *)
  (* firstn 1 nums = [2] *)
  (* skipn 1 ops = [] *)
  (* skipn 1 nums = [3] *)

  assert (eval_helper [] [2] 1 = 2).
  { simpl; reflexivity. }
  rewrite H.

  assert (eval_helper [] [3] 1 = 3).
  { simpl; reflexivity. }
  rewrite H.

  (* interp_op "^" 2 3 = 2^3 = 8 *)
  simpl.

  (* Now combine *)
  (* eval_helper ["^"] [2;3] 2 = 8 *)

  (* eval_helper ["^"; "*"] [2;3;4] 3 = interp_op "*" 8 4 = 32 *)

  (* eval_helper ["^"; "*"; "+"] [2;3;4;5] 4 = interp_op "+" 32 5 = 37 *)

  reflexivity.
Qed.
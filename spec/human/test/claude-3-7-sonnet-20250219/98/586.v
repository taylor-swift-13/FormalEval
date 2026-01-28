Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Open Scope string_scope.
Import ListNotations.

Definition is_uppercase_vowel_bool (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition count_upper_impl (s : string) : nat :=
  length (filter (fun i : nat =>
    match String.get i s with
    | Some c => andb (Nat.even i) (is_uppercase_vowel_bool c)
    | None => false
    end) (seq 0 (String.length s))).

Definition problem_98_pre (s : string) : Prop := True.

Definition problem_98_spec (s : string) (output : nat) : Prop :=
  output = count_upper_impl s.

Example problem_98_example :
  problem_98_spec "babcdGEFGHFjyOpQRstuVWx" 1.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "babcdGEFGHFjyOpQRstuVWx" = 23 *)
  (* seq 0 23 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22] *)
  (* i=0: get 0 'b' lower => false *)
  (* i=1: odd => false *)
  (* i=2: 'b' at 2? 'b' no uppercase vowel *)
  (* i=4: 'd' no *)
  (* i=6: 'G' uppercase but not vowel *)
  (* i=8: 'F' uppercase no vowel *)
  (* i=10:'H' uppercase no vowel *)
  (* i=12:'j' lower no *)
  (* i=14:'O' uppercase vowel, even idx 14 => true *)
  (* i=16:'Q' uppercase no vowel *)
  (* i=18:'s' lower no *)
  (* i=20:'V' uppercase no vowel *)
  (* So only index 14 counts, length 1 *)
  reflexivity.
Qed.
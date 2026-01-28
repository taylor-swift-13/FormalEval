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
  problem_98_spec "AbCdpEfGhIjKlMnOpQrStUvWxYz" 1.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "AbCdpEfGhIjKlMnOpQrStUvWxYz" = 26 *)
  (* seq 0 26 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25] *)
  (* Evaluate filter predicate for each index: *)
  (* i=0: get 0 = Some 'A'; even 0 = true; is_uppercase_vowel_bool 'A' = true -> keep *)
  (* i=1: odd index -> false *)
  (* i=2: 'C' uppercase consonant -> false *)
  (* i=3: odd index -> false *)
  (* i=4: 'p' lowercase -> false *)
  (* i=5: odd -> false *)
  (* i=6: 'E' uppercase vowel? check index 6 *)
  (* Wait carefully: string is "AbCdpEfGhIjKlMnOpQrStUvWxYz" *)
  (* Indices: 0='A',1='b',2='C',3='d',4='p',5='E',6='f',7='G',8='h',9='I',10='j',11='K',12='l',13='M',14='n',15='O',16='p',17='Q',18='r',19='S',20='t',21='U',22='v',23='W',24='x',25='Y',26='z' *)
  (* Note: length 26 means indices 0..25 *)
  (* i=0: 'A', even, vowel -> true *)
  (* i=2: 'C', even, consonant -> false *)
  (* i=4: 'p', even, lowercase -> false *)
  (* i=6: 'f', even, lowercase -> false *)
  (* i=8: 'h', even, lowercase -> false *)
  (* i=10: 'j', even, lowercase -> false *)
  (* i=12: 'l', even, lowercase -> false *)
  (* i=14: 'n', even, lowercase -> false *)
  (* i=16: 'p', even, lowercase -> false *)
  (* i=18: 'r', even, lowercase -> false *)
  (* i=20: 't', even, lowercase -> false *)
  (* i=22: 'v', even, lowercase -> false *)
  (* i=24: 'x', even, lowercase -> false *)
  (* So only index 0 matches *)
  reflexivity.
Qed.
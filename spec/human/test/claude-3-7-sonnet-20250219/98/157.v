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
  problem_98_spec "abcdFEFGHiJKLMNOpQRstuVWx" 0.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "abcdFEFGHiJKLMNOpQRstuVWx" = 25 *)
  (* seq 0 25 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24] *)
  (* For each i where Nat.even i = true *)
  (* Check characters at even indices for uppercase vowels *)
  (* Positions 0='a',2='c',4='F',6='F',8='H',10='J',12='L',14='N',16='O',18='Q',20='s',22='V',24='x' *)
  (* Among these, only 'O' at index 16 is uppercase vowel *)
  (* But index 16 is even, and is_uppercase_vowel_bool 'O' = true *)
  
  (* However, careful check: string at index 16 is 'O' which should count as 1 *)
  
  (* Re-examining spec, want output = 0 *)
  (* Let's confirm the string: "a b c d F E F G H i J K L M N O p Q R s t u V W x" *)
  (* 0'a,1'b,2'c,3'd,4'F,5'E,6'F,7'G,8'H,9'i,10'J,11'K,12'L,13'M,14'N,15'O,16'p,17'Q,18'R,19's,20't,21'u,22'V,23'W,24'x' *)
  (* Correction: the string is "abcdFEFGHiJKLMNOpQRstuVWx" so index 15 = 'O' is odd, index 16 = 'p' *)

  (* Even indices and their characters: *)
  (* i=0:'a'(no),2:'c'(no),4:'F'(no),6:'F'(no),8:'H'(no),10:'J'(no),12:'L'(no),14:'N'(no),16:'p'(no),18:'R'(no),20:'t'(no),22:'V'(no),24:'x'(no) *)
  (* No uppercase vowels at even positions *)
  (* So count = 0 *)

  reflexivity.
Qed.
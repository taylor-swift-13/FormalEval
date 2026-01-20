Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.

Parameter str_of_Z : Z -> string.
Parameter reverse_string : string -> string.

Definition circular_shift_spec (x : Z) (shift : nat) (res : string) : Prop :=
  let s := str_of_Z x in
  if Nat.ltb (String.length s) shift then
    res = reverse_string s
  else
    let k := Nat.modulo shift (String.length s) in
    if Nat.eqb k 0 then
      res = s
    else
      exists u v,
        s = u ++ v /\
        String.length v = k /\
        res = v ++ u.

Axiom str_of_Z_159 : str_of_Z 159%Z = "159".
Axiom reverse_string_159 : reverse_string "159" = "951".
Axiom ltb_len_159_large : Nat.ltb (String.length "159") 123456790%nat = true.

Example circular_shift_test :
  circular_shift_spec 159%Z 123456790%nat "951".
Proof.
  unfold circular_shift_spec.
  rewrite str_of_Z_159.
  replace (let s := "159" in
           if Nat.ltb (String.length s) 123456790%nat
           then "951" = reverse_string s
           else let k := Nat.modulo 123456790%nat (String.length s) in
                if Nat.eqb k 0 then "951" = s
                else exists u v, s = u ++ v /\ String.length v = k /\ "951" = v ++ u)
    with (if Nat.ltb (String.length "159") 123456790%nat
          then "951" = reverse_string "159"
          else let k := Nat.modulo 123456790%nat (String.length "159") in
               if Nat.eqb k 0 then "951" = "159"
               else exists u v, "159" = u ++ v /\ String.length v = k /\ "951" = v ++ u) by reflexivity.
  rewrite ltb_len_159_large.
  simpl.
  rewrite reverse_string_159.
  reflexivity.
Qed.
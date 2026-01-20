Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Definition ascii_code (c : ascii) : nat := nat_of_ascii c.

Definition is_upper (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 65 n) (Nat.leb n 90).

Definition is_lower (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_alpha (c : ascii) : bool := orb (is_upper c) (is_lower c).

Definition swapcase_char (c : ascii) : ascii :=
  let n := ascii_code c in
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else c.

Fixpoint string_map (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (string_map f s')
  end.

Fixpoint has_letter (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' => orb (is_alpha c) (has_letter s')
  end.

Fixpoint string_rev_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String b1 rest1 =>
    let n1 := ascii_code b1 in
    if andb (Nat.leb 240 n1) (Nat.leb n1 244)
    then
      match rest1 with
      | String b2 rest2 =>
        let n2 := ascii_code b2 in
        if andb (Nat.leb 128 n2) (Nat.leb n2 191)
        then
          match rest2 with
          | String b3 rest3 =>
            let n3 := ascii_code b3 in
            if andb (Nat.leb 128 n3) (Nat.leb n3 191)
            then
              match rest3 with
              | String b4 rest4 =>
                let n4 := ascii_code b4 in
                if andb (Nat.leb 128 n4) (Nat.leb n4 191)
                then string_rev_aux rest4 (String b1 (String b2 (String b3 (String b4 acc))))
                else string_rev_aux rest3 (String b1 (String b2 (String b3 acc)))
              | EmptyString => string_rev_aux rest2 (String b1 (String b2 acc))
              end
            else string_rev_aux rest2 (String b1 (String b2 acc))
          | EmptyString => string_rev_aux rest1 (String b1 acc)
          end
        else string_rev_aux rest1 (String b1 acc)
      | EmptyString => string_rev_aux rest1 (String b1 acc)
      end
    else string_rev_aux rest1 (String b1 acc)
  end.

Definition string_rev (s : string) : string := string_rev_aux s EmptyString.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = string_map swapcase_char s
  else r = string_rev s.

Example solve_spec_emoji : solve_spec ("😀😂😎"%string) ("😎😂😀"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.
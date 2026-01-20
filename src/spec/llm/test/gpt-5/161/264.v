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
  | String c s' => string_rev_aux s' (String c acc)
  end.

Definition string_rev (s : string) : string := string_rev_aux s EmptyString.

Fixpoint has_letter_utf8 (s : string) : bool :=
  match s with
  | EmptyString => false
  | String b1 s' =>
      if is_alpha b1 then true
      else match s' with
           | String b2 s'' =>
               let n1 := ascii_code b1 in
               let n2 := ascii_code b2 in
               if andb (Nat.eqb n1 208)
                       (orb (andb (Nat.leb 144 n2) (Nat.leb n2 175))
                            (andb (Nat.leb 176 n2) (Nat.leb n2 191)))
               then true
               else if andb (Nat.eqb n1 209) (andb (Nat.leb 128 n2) (Nat.leb n2 143))
               then true
               else has_letter_utf8 s'
           | _ => false
           end
  end.

Fixpoint swapcase_utf8 (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String b1 s' =>
      match s' with
      | String b2 s'' =>
          let n1 := ascii_code b1 in
          let n2 := ascii_code b2 in
          if andb (Nat.eqb n1 208) (andb (Nat.leb 144 n2) (Nat.leb n2 159)) then
            String (ascii_of_nat 208) (String (ascii_of_nat (n2 + 32)) (swapcase_utf8 s''))
          else if andb (Nat.eqb n1 208) (andb (Nat.leb 160 n2) (Nat.leb n2 175)) then
            String (ascii_of_nat 209) (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s''))
          else if andb (Nat.eqb n1 208) (andb (Nat.leb 176 n2) (Nat.leb n2 191)) then
            String (ascii_of_nat 208) (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s''))
          else if andb (Nat.eqb n1 209) (andb (Nat.leb 128 n2) (Nat.leb n2 143)) then
            String (ascii_of_nat 208) (String (ascii_of_nat (n2 + 32)) (swapcase_utf8 s''))
          else
            String (swapcase_char b1) (swapcase_utf8 s')
      | _ => String (swapcase_char b1) EmptyString
      end
  end.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter_utf8 s
  then r = swapcase_utf8 s
  else r = string_rev s.

Example solve_spec_new :
  solve_spec ("अমমুকтестоваяअমاختباअनु😀अম😂😎पماخاتبارلرুমলুল"%string)
             ("अমমুকТЕСТОВАЯअমاختباअनु😀अম😂😎पماخاتبارلرুমলুল"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.
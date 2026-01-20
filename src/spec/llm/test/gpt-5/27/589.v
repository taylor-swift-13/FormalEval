Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Local Open Scope string_scope.

Definition is_lower_nat (n : nat) : bool :=
  andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_upper_nat (n : nat) : bool :=
  andb (Nat.leb 65 n) (Nat.leb n 90).

Definition swap_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lower_nat n then
    Ascii.ascii_of_nat (n - 32)
  else if is_upper_nat n then
    Ascii.ascii_of_nat (n + 32)
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map_string f s')
  end.

Definition flip_case_spec (s : string) (res : string) : Prop :=
  res = map_string swap_ascii s.

Axiom flip_case_test:
  flip_case_spec
    "Карл у Кры укруукраукллал кораллы, а лКлportugués?укруалаQuiকpমoco.্েষেত্রwvm0cণউদাহরণক্্তета клpoco.арнет"
    "кАРЛ У кРЫ УКРУУКРАУКЛЛАЛ КОРАЛЛЫ, А ЛкЛPORTUGUÉS?УКРУАЛАqUIকPমOCO.্েষেত্রWVM0Cণউদাহরণক্্তЕТА КЛPOCO.АРНЕТ".

Example flip_case_new:
  flip_case_spec
    "Карл у Кры укруукраукллал кораллы, а лКлportugués?укруалаQuiকpমoco.্েষেত্রwvm0cণউদাহরণক্্তета клpoco.арнет"
    "кАРЛ У кРЫ УКРУУКРАУКЛЛАЛ КОРАЛЛЫ, А ЛкЛPORTUGUÉS?УКРУАЛАqUIকPমOCO.্েষেত্রWVM0Cণউদাহরণক্্তЕТА КЛPOCO.АРНЕТ".
Proof.
  exact flip_case_test.
Qed.
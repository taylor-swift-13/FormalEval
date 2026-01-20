
Require Import List.
Require Import ZArith.
Import ListNotations.

Definition prod_signs_spec (arr : list Z) (res : option Z) : Prop :=
  match arr with
  | [] => res = None
  | _ =>
    if List.existsb (fun x => Z.eqb x 0) arr then
      res = Some 0
    else
      let s := fold_left (fun acc x => acc + Z.abs x) arr 0 in
      let sgn := fold_left (fun acc x => acc * (Z.quot x (Z.abs x))) arr 1 in
      res = Some (s * sgn)
  end.

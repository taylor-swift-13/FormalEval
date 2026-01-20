
Require Import List.
Import ListNotations.
Require Import Reals.
Open Scope R_scope.

Definition rescale_to_unit_spec (numbers rescaled : list R) : Prop :=
  length numbers >= 2 /\
  In (Rmin_list numbers) numbers /\
  In (Rmax_list numbers) numbers /\
  let ma := Rmax_list numbers in
  let mi := Rmin_list numbers in
  let k := / (ma - mi) in
  (* For every element x in numbers and corresponding element y in rescaled, y = (x - mi) * k *)
  Forall2 (fun x y => y = (x - mi) * k) numbers rescaled /\
  (* The minimum of rescaled is 0 *)
  In 0 rescaled /\
  (* The maximum of rescaled is 1 *)
  In 1 rescaled.

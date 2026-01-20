
Require Import List.
Require Import Reals.

Definition rescale_to_unit_spec (numbers : list R) (result : list R) : Prop :=
  length numbers >= 2 /\
  let ma := fold_right Rmax (hd 0 numbers) numbers in
  let mi := fold_right Rmin (hd 0 numbers) numbers in
  let k := 1 / (ma - mi) in
  result = map (fun x => (x - mi) * k) numbers /\
  ma = fold_right Rmax (hd 0 numbers) numbers /\
  mi = fold_right Rmin (hd 0 numbers) numbers.

module E = Sexpr.Expr
module Nodes = Sexpr.BvTbl

type t = { width : int; zeros : Z.t; ones : Z.t }

let mask width = Z.pred (Z.shift_left Z.one width)
let make width zeros ones =
  let m = mask width in
  let zeros = Z.logand zeros m and ones = Z.logand ones m in
  { width; zeros = Z.logand zeros (Z.lognot ones); ones }
let unknown width = make width Z.zero Z.zero
let possible_ones value = Z.logand (mask value.width) (Z.lognot value.zeros)
let disjoint left right =
  left.width = right.width
  && Z.equal (Z.logand (possible_ones left) (possible_ones right)) Z.zero
let is_constant value =
  if Z.equal (Z.logor value.zeros value.ones) (mask value.width)
  then Some value.ones else None

let trailing_zeros value =
  let rec loop index =
    if index >= value.width || not (Z.testbit value.zeros index) then index
    else loop (index + 1)
  in loop 0

let analyze expression =
  let memo = Nodes.create 128 in
  let rec visit node =
    match Nodes.find_opt memo node with
    | Some result -> result
    | None ->
        let width = E.sizeof node and m = mask (E.sizeof node) in
        let result =
          match node with
          | E.Cst value ->
              let ones = Bitvector.value_of value in
              make width (Z.logxor m ones) ones
          | E.Var _ | E.Load _ -> unknown width
          | E.Unary { f = E.Not; x; _ } ->
              let x = visit x in make width x.ones x.zeros
          | E.Unary { f = E.Minus; _ } -> unknown width
          | E.Unary { f = E.Uext amount; x; _ } ->
              let x = visit x in
              let high = Z.shift_left (Z.pred (Z.shift_left Z.one amount)) x.width in
              make width (Z.logor x.zeros high) x.ones
          | E.Unary { f = E.Sext amount; x; _ } ->
              let x = visit x in
              let sign = x.width - 1 in
              let high = Z.shift_left (Z.pred (Z.shift_left Z.one amount)) x.width in
              let zeros = if Z.testbit x.zeros sign then Z.logor x.zeros high else x.zeros in
              let ones = if Z.testbit x.ones sign then Z.logor x.ones high else x.ones in
              make width zeros ones
          | E.Unary { f = E.Restrict { lo; hi }; x; _ } ->
              let x = visit x in
              let sub = mask (hi - lo + 1) in
              make width (Z.logand (Z.shift_right x.zeros lo) sub)
                (Z.logand (Z.shift_right x.ones lo) sub)
          | E.Binary { f = E.And; x; y; _ } ->
              let x = visit x and y = visit y in
              make width (Z.logor x.zeros y.zeros) (Z.logand x.ones y.ones)
          | E.Binary { f = E.Or; x; y; _ } ->
              let x = visit x and y = visit y in
              make width (Z.logand x.zeros y.zeros) (Z.logor x.ones y.ones)
          | E.Binary { f = E.Xor; x; y; _ } ->
              let x = visit x and y = visit y in
              make width
                (Z.logor (Z.logand x.zeros y.zeros) (Z.logand x.ones y.ones))
                (Z.logor (Z.logand x.zeros y.ones) (Z.logand x.ones y.zeros))
          | E.Binary { f = E.Plus; x; y; _ } ->
              let x = visit x and y = visit y in
              if disjoint x y then
                make width (Z.logand x.zeros y.zeros) (Z.logor x.ones y.ones)
              else unknown width
          | E.Binary { f = E.Mul; x; y; _ } ->
              let x = visit x and y = visit y in
              let count = min width (trailing_zeros x + trailing_zeros y) in
              make width (Z.pred (Z.shift_left Z.one count)) Z.zero
          | E.Binary { f = (E.Lsl | E.Lsr | E.Asr as operation); x;
                       y = E.Cst amount; _ } ->
              let x = visit x and amount = Bitvector.value_of amount in
              if Z.geq amount (Z.of_int x.width) then
                if operation = E.Asr && Z.testbit x.ones (x.width - 1)
                then make width Z.zero m else make width m Z.zero
              else
                let amount = Z.to_int amount in
                if operation = E.Lsl then
                  make width
                    (Z.logor (Z.logand m (Z.shift_left x.zeros amount))
                       (Z.pred (Z.shift_left Z.one amount)))
                    (Z.logand m (Z.shift_left x.ones amount))
                else if operation = E.Lsr then
                  let high = Z.logand m
                      (Z.lognot (Z.pred (Z.shift_left Z.one (width - amount)))) in
                  make width (Z.logor (Z.shift_right x.zeros amount) high)
                    (Z.shift_right x.ones amount)
                else
                  let sign = width - 1 in
                  let high = Z.logand m
                      (Z.lognot (Z.pred (Z.shift_left Z.one (width - amount)))) in
                  let zeros = Z.shift_right x.zeros amount
                  and ones = Z.shift_right x.ones amount in
                  make width
                    (if Z.testbit x.zeros sign then Z.logor zeros high else zeros)
                    (if Z.testbit x.ones sign then Z.logor ones high else ones)
          | E.Ite { c; t; e; _ } ->
              let c = visit c in
              (match is_constant c with
              | Some value when Z.equal value Z.zero -> visit e
              | Some _ -> visit t
              | None ->
                  let t = visit t and e = visit e in
                  make width (Z.logand t.zeros e.zeros) (Z.logand t.ones e.ones))
          | _ -> unknown width
        in
        Nodes.add memo node result;
        result
  in
  visit expression

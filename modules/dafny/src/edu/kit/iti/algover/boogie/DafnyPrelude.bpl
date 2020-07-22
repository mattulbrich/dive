// Dafny prelude
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Edited sequence axioms 20 October 2009 by Alex Summers.
// Modified 2014 by Dan Rosen.
// Copyright (c) 2008-2014, Microsoft.

// Adapted for AlgoVer

//D const $$Language$Dafny: bool;  // To be recognizable to the ModelViewer as
//D axiom $$Language$Dafny;        // coming from a Dafny program.

// ---------------------------------------------------------------
// -- Types ------------------------------------------------------
// ---------------------------------------------------------------

type Ty;
//D type Bv0 = int;

const unique TBool : Ty;
//D const unique TChar : Ty;
const unique TInt  : Ty;
//D const unique TReal : Ty;
//D const unique TORDINAL  : Ty;
//D function TBitvector(int) : Ty;
function TSet(Ty)      : Ty;
//D function TISet(Ty)     : Ty;
function TMultiSet(Ty) : Ty;
function TSeq(Ty)      : Ty;
//D function TMap(Ty, Ty)  : Ty;
//D function TIMap(Ty, Ty) : Ty;

const unique THeap : Ty;
function TField(Ty)      : Ty;
function TArray(Ty)      : Ty;
function TArray2(Ty)      : Ty;

//D function Inv0_TBitvector(Ty) : int;
//D axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);
function Inv0_TSet(Ty) : Ty;
axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);
//D function Inv0_TISet(Ty) : Ty;
//D axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);
function Inv0_TSeq(Ty) : Ty;
axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);
function Inv0_TMultiSet(Ty) : Ty;
axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);
//D function Inv0_TMap(Ty) : Ty;
//D function Inv1_TMap(Ty) : Ty;
//D axiom (forall t, u: Ty :: { TMap(t,u) } Inv0_TMap(TMap(t,u)) == t);
//D axiom (forall t, u: Ty :: { TMap(t,u) } Inv1_TMap(TMap(t,u)) == u);
//D function Inv0_TIMap(Ty) : Ty;
//D function Inv1_TIMap(Ty) : Ty;
//D axiom (forall t, u: Ty :: { TIMap(t,u) } Inv0_TIMap(TIMap(t,u)) == t);
//D axiom (forall t, u: Ty :: { TIMap(t,u) } Inv1_TIMap(TIMap(t,u)) == u);
function Inv0_TArray(Ty) : Ty;
axiom (forall t: Ty :: { TArray(t) } Inv0_TArray(TArray(t)) == t);
axiom (forall x: ref :: (forall t: Ty :: $Is(x, TArray(t)) <==> dtype(x) == TArray(t) || x == null));

// -- Classes and Datatypes --

// -- Type Tags --
//D type TyTag;
//D function Tag(Ty) : TyTag;
//D
//D const unique TagBool     : TyTag;
//D const unique TagChar     : TyTag;
//D const unique TagInt      : TyTag;
//D const unique TagReal     : TyTag;
//D const unique TagORDINAL  : TyTag;
//D const unique TagSet      : TyTag;
//D const unique TagISet     : TyTag;
//D const unique TagMultiSet : TyTag;
//D const unique TagSeq      : TyTag;
//D const unique TagMap      : TyTag;
//D const unique TagIMap     : TyTag;
//D const unique TagClass    : TyTag;
//D
//D axiom Tag(TBool) == TagBool;
//D axiom Tag(TChar) == TagChar;
//D axiom Tag(TInt) == TagInt;
//D axiom Tag(TReal) == TagReal;
//D axiom Tag(TORDINAL) == TagORDINAL;
//D axiom (forall t: Ty    :: { TSet(t) }      Tag(TSet(t))      == TagSet);
//D axiom (forall t: Ty    :: { TISet(t) }     Tag(TISet(t))     == TagISet);
//D axiom (forall t: Ty    :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);
//D axiom (forall t: Ty    :: { TSeq(t) }      Tag(TSeq(t))      == TagSeq);
//D axiom (forall t, u: Ty :: { TMap(t,u) }    Tag(TMap(t,u))    == TagMap);
//D axiom (forall t, u: Ty :: { TIMap(t,u) }   Tag(TIMap(t,u))   == TagIMap);

// ---------------------------------------------------------------
// -- Literals ---------------------------------------------------
// ---------------------------------------------------------------
//D function {:identity} LitInt(x: int): int { x }
//D axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)) );
//D function {:identity} LitReal(x: real): real { x }
//D axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)) );
//D function {:identity} Lit<T>(x: T): T { x }
//D axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)) );

// ---------------------------------------------------------------
// -- Characters -------------------------------------------------
// ---------------------------------------------------------------

//D type char;
//D function char#FromInt(int): char;
//D function char#ToInt(char): int;  // inverse of char#FromInt
//D axiom (forall ch: char ::
//D   { char#ToInt(ch) }
//D   char#FromInt(char#ToInt(ch)) == ch &&
//D   0 <= char#ToInt(ch) && char#ToInt(ch) < 65536);
//D axiom (forall n: int ::
//D   { char#FromInt(n) }
//D   0 <= n && n < 65536 ==> char#ToInt(char#FromInt(n)) == n);
//D
//D function char#Plus(char, char): char;
//D function char#Minus(char, char): char;
//D axiom (forall a: char, b: char ::
//D   { char#Plus(a, b) }
//D   char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));
//D axiom (forall a: char, b: char ::
//D   { char#Minus(a, b) }
//D   char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));

// ---------------------------------------------------------------
// -- References -------------------------------------------------
// ---------------------------------------------------------------

type ref;
const null: ref;

// ---------------------------------------------------------------
// -- Traits -----------------------------------------------------
// ---------------------------------------------------------------

//D const unique NoTraitAtAll: ClassName;
//D function TraitParent(ClassName): ClassName;

// ---------------------------------------------------------------
// -- Boxing and unboxing ----------------------------------------
// ---------------------------------------------------------------

//D type Box;
//D const $ArbitraryBoxValue: Box;
//D
//D function $Box<T>(T): Box;
//D function $Unbox<T>(Box): T;
//D
//D axiom (forall<T> x : T :: { $Box(x) } $Unbox($Box(x)) == x);
//D
//D axiom (forall bx : Box ::
//D     { $IsBox(bx, TInt) }
//D     ( $IsBox(bx, TInt) ==> $Box($Unbox(bx) : int) == bx && $Is($Unbox(bx) : int, TInt)));
//D axiom (forall bx : Box ::
//D     { $IsBox(bx, TReal) }
//D     ( $IsBox(bx, TReal) ==> $Box($Unbox(bx) : real) == bx && $Is($Unbox(bx) : real, TReal)));
//D axiom (forall bx : Box ::
//D     { $IsBox(bx, TBool) }
//D     ( $IsBox(bx, TBool) ==> $Box($Unbox(bx) : bool) == bx && $Is($Unbox(bx) : bool, TBool)));
//D axiom (forall bx : Box ::
//D     { $IsBox(bx, TChar) }
//D     ( $IsBox(bx, TChar) ==> $Box($Unbox(bx) : char) == bx && $Is($Unbox(bx) : char, TChar)));
//D axiom (forall bx : Box, t : Ty ::
//D     { $IsBox(bx, TSet(t)) }
//D     ( $IsBox(bx, TSet(t)) ==> $Box($Unbox(bx) : Set Box) == bx && $Is($Unbox(bx) : Set Box, TSet(t))));
//D axiom (forall bx : Box, t : Ty ::
//D     { $IsBox(bx, TISet(t)) }
//D     ( $IsBox(bx, TISet(t)) ==> $Box($Unbox(bx) : ISet Box) == bx && $Is($Unbox(bx) : ISet Box, TISet(t))));
//D axiom (forall bx : Box, t : Ty ::
//D     { $IsBox(bx, TMultiSet(t)) }
//D     ( $IsBox(bx, TMultiSet(t)) ==> $Box($Unbox(bx) : MultiSet Box) == bx && $Is($Unbox(bx) : MultiSet Box, TMultiSet(t))));
//D axiom (forall bx : Box, t : Ty ::
//D     { $IsBox(bx, TSeq(t)) }
//D     ( $IsBox(bx, TSeq(t)) ==> $Box($Unbox(bx) : Seq Box) == bx && $Is($Unbox(bx) : Seq Box, TSeq(t))));
//D axiom (forall bx : Box, s : Ty, t : Ty ::
//D     { $IsBox(bx, TMap(s, t)) }
//D     ( $IsBox(bx, TMap(s, t)) ==> $Box($Unbox(bx) : Map Box Box) == bx && $Is($Unbox(bx) : Map Box Box, TMap(s, t))));
//D axiom (forall bx : Box, s : Ty, t : Ty ::
//D     { $IsBox(bx, TIMap(s, t)) }
//D     ( $IsBox(bx, TIMap(s, t)) ==> $Box($Unbox(bx) : IMap Box Box) == bx && $Is($Unbox(bx) : IMap Box Box, TIMap(s, t))));
//D
//D axiom (forall<T> v : T, t : Ty ::
//D     { $IsBox($Box(v), t) }
//D     ( $IsBox($Box(v), t) <==> $Is(v,t) ));
//D axiom (forall<T> v : T, t : Ty, h : Heap ::
//D     { $IsAllocBox($Box(v), t, h) }
//D     ( $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v,t,h) ));

// ---------------------------------------------------------------
// -- Is and IsAlloc ---------------------------------------------
// ---------------------------------------------------------------

// Type-argument to $Is is the /representation type/,
// the second value argument to $Is is the actual type.
function $Is<T>(T,Ty): bool;           // no heap for now
//D function $IsAlloc<T>(T,Ty,Heap): bool;


// MU added this which as originally wrong
axiom (forall<T> f: Field T, t0: Ty :: { $Is(f, TField(t0)) }
  $Is(f, TField(t0)) ==>
  (forall h: Heap, o: ref :: { read(h, o, f) } $IsGoodHeap(h) ==> $Is(read(h, o, f), t0)));


// Corresponding entries for boxes...
// This could probably be solved by having Box also inhabit Ty
//D function $IsBox<T>(T,Ty): bool;
//D function $IsAllocBox<T>(T,Ty,Heap): bool;

//D axiom(forall v : int  :: { $Is(v,TInt) }  $Is(v,TInt));
//D axiom(forall v : real :: { $Is(v,TReal) } $Is(v,TReal));
//D axiom(forall v : bool :: { $Is(v,TBool) } $Is(v,TBool));
//D axiom(forall v : char :: { $Is(v,TChar) } $Is(v,TChar));
//D axiom(forall v : ORDINAL :: { $Is(v,TORDINAL) } $Is(v,TORDINAL));

//D axiom(forall h : Heap, v : int  :: { $IsAlloc(v,TInt,h) }  $IsAlloc(v,TInt,h));
//D axiom(forall h : Heap, v : real :: { $IsAlloc(v,TReal,h) } $IsAlloc(v,TReal,h));
//D axiom(forall h : Heap, v : bool :: { $IsAlloc(v,TBool,h) } $IsAlloc(v,TBool,h));
//D axiom(forall h : Heap, v : char :: { $IsAlloc(v,TChar,h) } $IsAlloc(v,TChar,h));
//D axiom(forall h : Heap, v : ORDINAL :: { $IsAlloc(v,TORDINAL,h) } $IsAlloc(v,TORDINAL,h));

axiom (forall<T> v: Set T, t0: Ty :: { $Is(v, TSet(t0)) }
  $Is(v, TSet(t0)) <==>
  (forall x: T :: { v[x] } v[x] ==> $Is(x, t0)));
//D axiom (forall v: Set Box, t0: Ty :: { $Is(v, TSet(t0)) }
//D   $Is(v, TSet(t0)) <==>
//D   (forall bx: Box :: { v[bx] }
//D     v[bx] ==> $IsBox(bx, t0)));
//D axiom (forall v: ISet Box, t0: Ty :: { $Is(v, TISet(t0)) }
//D   $Is(v, TISet(t0)) <==>
//D   (forall bx: Box :: { v[bx] }
//D     v[bx] ==> $IsBox(bx, t0)));
//D axiom (forall v: MultiSet Box, t0: Ty :: { $Is(v, TMultiSet(t0)) }
//D   $Is(v, TMultiSet(t0)) <==>
//D   (forall bx: Box :: { v[bx] }
//D     0 < v[bx] ==> $IsBox(bx, t0)));
//D axiom (forall v: MultiSet Box, t0: Ty :: { $Is(v, TMultiSet(t0)) }
//D   $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));
axiom (forall<T> v: MultiSet T, t0: Ty :: { $Is(v, TMultiSet(t0)) }
  $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));
axiom (forall<T> v: Seq T, t0: Ty :: { $Is(v, TSeq(t0)) }
  $Is(v, TSeq(t0)) <==>
  (forall i : int :: { Seq#Index(v, i) }
     0 <= i && i < Seq#Length(v) ==> $Is(Seq#Index(v, i), t0)));
// MU: delete range guard?

//D axiom (forall v: Seq Box, t0: Ty :: { $Is(v, TSeq(t0)) }
//D   $Is(v, TSeq(t0)) <==>
//D   (forall i : int :: { Seq#Index(v, i) }
//D     0 <= i && i < Seq#Length(v) ==>
//D 	$IsBox(Seq#Index(v, i), t0)));
//D axiom (forall v: Set Box, t0: Ty, h: Heap :: { $IsAlloc(v, TSet(t0), h) }
//D   $IsAlloc(v, TSet(t0), h) <==>
//D   (forall bx: Box :: { v[bx] }
//D     v[bx] ==> $IsAllocBox(bx, t0, h)));
//D axiom (forall v: ISet Box, t0: Ty, h: Heap :: { $IsAlloc(v, TISet(t0), h) }
//D   $IsAlloc(v, TISet(t0), h) <==>
//D   (forall bx: Box :: { v[bx] }
//D     v[bx] ==> $IsAllocBox(bx, t0, h)));
//D axiom (forall v: MultiSet Box, t0: Ty, h: Heap :: { $IsAlloc(v, TMultiSet(t0), h) }
//D   $IsAlloc(v, TMultiSet(t0), h) <==>
//D   (forall bx: Box :: { v[bx] }
//D     0 < v[bx] ==> $IsAllocBox(bx, t0, h)));
//D axiom (forall v: Seq Box, t0: Ty, h: Heap :: { $IsAlloc(v, TSeq(t0), h) }
//D   $IsAlloc(v, TSeq(t0), h) <==>
//D   (forall i : int :: { Seq#Index(v, i) }
//D     0 <= i && i < Seq#Length(v) ==>
//D 	$IsAllocBox(Seq#Index(v, i), t0, h)));
//D
//D axiom (forall v: Map Box Box, t0: Ty, t1: Ty ::
//D   { $Is(v, TMap(t0, t1)) }
//D   $Is(v, TMap(t0, t1))
//D      <==> (forall bx: Box ::
//D       { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
//D       Map#Domain(v)[bx] ==>
//D         $IsBox(Map#Elements(v)[bx], t1) &&
//D         $IsBox(bx, t0)));
//D axiom (forall v: Map Box Box, t0: Ty, t1: Ty, h: Heap ::
//D   { $IsAlloc(v, TMap(t0, t1), h) }
//D   $IsAlloc(v, TMap(t0, t1), h)
//D      <==> (forall bx: Box ::
//D       { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
//D       Map#Domain(v)[bx] ==>
//D         $IsAllocBox(Map#Elements(v)[bx], t1, h) &&
//D         $IsAllocBox(bx, t0, h)));
//D
//D axiom (forall v: IMap Box Box, t0: Ty, t1: Ty ::
//D   { $Is(v, TIMap(t0, t1)) }
//D   $Is(v, TIMap(t0, t1))
//D      <==> (forall bx: Box ::
//D       { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
//D       IMap#Domain(v)[bx] ==>
//D         $IsBox(IMap#Elements(v)[bx], t1) &&
//D         $IsBox(bx, t0)));
//D axiom (forall v: IMap Box Box, t0: Ty, t1: Ty, h: Heap ::
//D   { $IsAlloc(v, TIMap(t0, t1), h) }
//D   $IsAlloc(v, TIMap(t0, t1), h)
//D      <==> (forall bx: Box ::
//D       { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
//D       IMap#Domain(v)[bx] ==>
//D         $IsAllocBox(IMap#Elements(v)[bx], t1, h) &&
//D         $IsAllocBox(bx, t0, h)));

// ---------------------------------------------------------------
// -- Encoding of type names -------------------------------------
// ---------------------------------------------------------------

//D type ClassName;
//D const unique class._System.int: ClassName;
//D const unique class._System.bool: ClassName;
//D const unique class._System.set: ClassName;
//D const unique class._System.seq: ClassName;
//D const unique class._System.multiset: ClassName;
//D
//D function Tclass._System.object?(): Ty;
const unique TObject : Ty;

function /*{:never_pattern true}*/ dtype(ref): Ty; // changed from ClassName to Ty

//D function TypeTuple(a: ClassName, b: ClassName): ClassName;
//D function TypeTupleCar(ClassName): ClassName;
//D function TypeTupleCdr(ClassName): ClassName;
//D // TypeTuple is injective in both arguments:
//D axiom (forall a: ClassName, b: ClassName :: { TypeTuple(a,b) }
//D   TypeTupleCar(TypeTuple(a,b)) == a &&
//D   TypeTupleCdr(TypeTuple(a,b)) == b);

// -- Function handles -------------------------------------------

//D type HandleType;
//D
//D function SetRef_to_SetBox(s: [ref]bool): Set Box;
//D axiom (forall s: [ref]bool, bx: Box :: { SetRef_to_SetBox(s)[bx] }
//D   SetRef_to_SetBox(s)[bx] == s[$Unbox(bx): ref]);
//D axiom (forall s: [ref]bool :: { SetRef_to_SetBox(s) }
//D   $Is(SetRef_to_SetBox(s), TSet(Tclass._System.object?())));

// ---------------------------------------------------------------
// -- Datatypes --------------------------------------------------
// ---------------------------------------------------------------

//D type DatatypeType;
//D
//D type DtCtorId;
//D function DatatypeCtorId(DatatypeType): DtCtorId;
//D
//D function DtRank(DatatypeType): int;
//D function BoxRank(Box): int;
//D
//D axiom (forall d: DatatypeType :: {BoxRank($Box(d))} BoxRank($Box(d)) == DtRank(d));

// ---------------------------------------------------------------
// -- Big Ordinals -----------------------------------------------
// ---------------------------------------------------------------

//D type ORDINAL = Box;  // :| There are more big ordinals than boxes
//D
//D // The following two functions give an abstracton over all ordinals.
//D // Function ORD#IsNat returns true when the ordinal is one of the natural
//D // numbers.  Function ORD#Offset gives how many successors (that is,
//D // +1 operations) an ordinal is above the nearest lower limit ordinal.
//D // That is, if the ordinal is \lambda+n, then ORD#Offset returns n.
//D function ORD#IsNat(ORDINAL): bool;
//D function ORD#Offset(ORDINAL): int;
//D axiom (forall o:ORDINAL :: { ORD#Offset(o) } 0 <= ORD#Offset(o));
//D
//D function {:inline} ORD#IsLimit(o: ORDINAL): bool { ORD#Offset(o) == 0 }
//D function {:inline} ORD#IsSucc(o: ORDINAL): bool { 0 < ORD#Offset(o) }
//D
//D function ORD#FromNat(int): ORDINAL;
//D axiom (forall n:int :: { ORD#FromNat(n) }
//D   0 <= n ==> ORD#IsNat(ORD#FromNat(n)) && ORD#Offset(ORD#FromNat(n)) == n);
//D axiom (forall o:ORDINAL :: { ORD#Offset(o) } { ORD#IsNat(o) }
//D   ORD#IsNat(o) ==> o == ORD#FromNat(ORD#Offset(o)));
//D
//D function ORD#Less(ORDINAL, ORDINAL): bool;
//D axiom (forall o,p: ORDINAL :: { ORD#Less(o,p) }
//D   (ORD#Less(o,p) ==> o != p) &&  // irreflexivity
//D   (ORD#IsNat(o) && !ORD#IsNat(p) ==> ORD#Less(o,p)) &&
//D   (ORD#IsNat(o) && ORD#IsNat(p) ==> ORD#Less(o,p) == (ORD#Offset(o) < ORD#Offset(p))));
//D // ORD#Less is irreflexive:
//D axiom (forall o,p: ORDINAL :: { ORD#Less(o,p) }
//D   ORD#Less(o,p) ==> o != p);
//D // ORD#Less is trichotomous:
//D axiom (forall o,p: ORDINAL :: { ORD#Less(o,p), ORD#Less(p,o) }
//D   ORD#Less(o,p) || o == p || ORD#Less(p,o));
//D // ORD#Less is transitive:
//D axiom (forall o,p,r: ORDINAL ::
//D   { ORD#Less(o,p), ORD#Less(p,r) }
//D   { ORD#Less(o,p), ORD#Less(o,r) }
//D   ORD#Less(o,p) && ORD#Less(p,r) ==> ORD#Less(o,r));
//D
//D // ORD#LessThanLimit is a synonym of ORD#Less, introduced for more selected triggering
//D function ORD#LessThanLimit(ORDINAL, ORDINAL): bool;
//D axiom (forall o,p: ORDINAL :: { ORD#LessThanLimit(o, p) }
//D   ORD#LessThanLimit(o, p) == ORD#Less(o, p));
//D
//D function ORD#Plus(ORDINAL, ORDINAL): ORDINAL;
//D axiom (forall o,p: ORDINAL :: { ORD#Plus(o,p) }
//D   (ORD#IsNat(ORD#Plus(o,p)) ==> ORD#IsNat(o) && ORD#IsNat(p)) &&
//D   (ORD#IsNat(p) ==>
//D     ORD#IsNat(ORD#Plus(o,p)) == ORD#IsNat(o) &&
//D     ORD#Offset(ORD#Plus(o,p)) == ORD#Offset(o) + ORD#Offset(p)));
//D axiom (forall o,p: ORDINAL :: { ORD#Plus(o,p) }
//D   (o == ORD#Plus(o, p) || ORD#Less(o, ORD#Plus(o, p))) &&
//D   (p == ORD#Plus(o, p) || ORD#Less(p, ORD#Plus(o, p))));
//D axiom (forall o,p: ORDINAL :: { ORD#Plus(o,p) }
//D   (o == ORD#FromNat(0) ==> ORD#Plus(o, p) == p) &&
//D   (p == ORD#FromNat(0) ==> ORD#Plus(o, p) == o));
//D
//D function ORD#Minus(ORDINAL, ORDINAL): ORDINAL;
//D axiom (forall o,p: ORDINAL :: { ORD#Minus(o,p) }
//D   ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o) ==>
//D     ORD#IsNat(ORD#Minus(o,p)) == ORD#IsNat(o) &&
//D     ORD#Offset(ORD#Minus(o,p)) == ORD#Offset(o) - ORD#Offset(p));
//D axiom (forall o,p: ORDINAL :: { ORD#Minus(o,p) }
//D   ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o) ==>
//D     (p == ORD#FromNat(0) && ORD#Minus(o, p) == o) ||
//D     (p != ORD#FromNat(0) && ORD#Less(ORD#Minus(o, p), o)));
//D
//D // o+m+n == o+(m+n)
//D axiom (forall o: ORDINAL, m,n: int ::
//D   { ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
//D   0 <= m && 0 <= n ==>
//D   ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Plus(o, ORD#FromNat(m+n)));
//D // o-m-n == o+(m+n)
//D axiom (forall o: ORDINAL, m,n: int ::
//D   { ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
//D   0 <= m && 0 <= n && m+n <= ORD#Offset(o) ==>
//D   ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Minus(o, ORD#FromNat(m+n)));
//D // o+m-n == EITHER o+(m-n) OR o-(n-m)
//D axiom (forall o: ORDINAL, m,n: int ::
//D   { ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
//D   0 <= m && 0 <= n && n <= ORD#Offset(o) + m ==>
//D     (0 <= m - n ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Plus(o, ORD#FromNat(m-n))) &&
//D     (m - n <= 0 ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Minus(o, ORD#FromNat(n-m))));
//D // o-m+n == EITHER o-(m-n) OR o+(n-m)
//D axiom (forall o: ORDINAL, m,n: int ::
//D   { ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) }
//D   0 <= m && 0 <= n && n <= ORD#Offset(o) + m ==>
//D     (0 <= m - n ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Minus(o, ORD#FromNat(m-n))) &&
//D     (m - n <= 0 ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) == ORD#Plus(o, ORD#FromNat(n-m))));

// ---------------------------------------------------------------
// -- Axiom contexts ---------------------------------------------
// ---------------------------------------------------------------

// used to make sure function axioms are not used while their consistency is being checked
//D const $ModuleContextHeight: int;
//D const $FunctionContextHeight: int;

// ---------------------------------------------------------------
// -- Layers of function encodings -------------------------------
// ---------------------------------------------------------------

//D type LayerType;
//D const $LZ: LayerType;
//D function $LS(LayerType): LayerType;
//D function AsFuelBottom(LayerType) : LayerType;
//D
//D function AtLayer<A>([LayerType]A, LayerType): A;
//D axiom (forall<A> f : [LayerType]A, ly : LayerType :: { AtLayer(f,ly) } AtLayer(f,ly) == f[ly]);
//D axiom (forall<A> f : [LayerType]A, ly : LayerType :: { AtLayer(f,$LS(ly)) } AtLayer(f,$LS(ly)) == AtLayer(f,ly));

// ---------------------------------------------------------------
// -- Fields -----------------------------------------------------
// ---------------------------------------------------------------

type Field alpha;

//D function FDim<T>(Field T): int;

function IndexField<alpha>(int): Field alpha;
function IndexField2<alpha>(int, int): Field alpha;
//D axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);
function IndexField_Inverse<T>(Field T): int;
axiom (forall<T> i: int :: { IndexField(i) : Field T } IndexField_Inverse(IndexField(i) : Field T) == i);
function IndexField2_Inverse0<T>(Field T): int;
axiom (forall<T> i,j: int :: { IndexField2(i,j) : Field T } IndexField_Inverse(IndexField2(i,j) : Field T) == i);
function IndexField2_Inverse1<T>(Field T): int;
axiom (forall<T> i,j: int :: { IndexField2(i,j) : Field T } IndexField_Inverse(IndexField2(i,j) : Field T) == j);

//D function MultiIndexField(Field Box, int): Field Box;
//D axiom (forall f: Field Box, i: int :: { MultiIndexField(f,i) } FDim(MultiIndexField(f,i)) == FDim(f) + 1);
//D function MultiIndexField_Inverse0<T>(Field T): Field T;
//D function MultiIndexField_Inverse1<T>(Field T): int;
//D axiom (forall f: Field Box, i: int :: { MultiIndexField(f,i) }
//D   MultiIndexField_Inverse0(MultiIndexField(f,i)) == f &&
//D   MultiIndexField_Inverse1(MultiIndexField(f,i)) == i);

//D function DeclType<T>(Field T): ClassName;
//D
//D type NameFamily;
//D function DeclName<T>(Field T): NameFamily;
//D function FieldOfDecl<alpha>(ClassName, NameFamily): Field alpha;
//D axiom (forall<T> cl : ClassName, nm: NameFamily ::
//D    {FieldOfDecl(cl, nm): Field T}
//D    DeclType(FieldOfDecl(cl, nm): Field T) == cl && DeclName(FieldOfDecl(cl, nm): Field T) == nm);
//D
//D function $IsGhostField<T>(Field T): bool;

// ---------------------------------------------------------------
// -- Allocatedness and Heap Succession --------------------------
// ---------------------------------------------------------------

// $IsAlloc and $IsAllocBox are monotonic

//D axiom(forall<T> h, k : Heap, v : T, t : Ty ::
//D   { $HeapSucc(h, k), $IsAlloc(v, t, h) }
//D   $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));
//D axiom(forall h, k : Heap, bx : Box, t : Ty ::
//D   { $HeapSucc(h, k), $IsAllocBox(bx, t, h) }
//D   $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

// No axioms for $Is and $IsBox since they don't talk about the heap.

//D const unique alloc: Field bool;
//D const unique allocName: NameFamily;
//D axiom FDim(alloc) == 0 &&
//D   DeclName(alloc) == allocName &&
//D   !$IsGhostField(alloc);  // treat as non-ghost field, because it cannot be changed by ghost code

// ---------------------------------------------------------------
// -- Arrays -----------------------------------------------------
// ---------------------------------------------------------------

function _System.array.Length(a: ref): int;
axiom (forall o: ref :: 0 <= _System.array.Length(o));

// ---------------------------------------------------------------
// -- Reals ------------------------------------------------------
// ---------------------------------------------------------------

//D function Int(x: real): int { int(x) }
//D function Real(x: int): real { real(x) }
//D axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i);
//D
//D function {:inline} _System.real.Floor(x: real): int { Int(x) }

// ---------------------------------------------------------------
// -- The heap ---------------------------------------------------
// ---------------------------------------------------------------

type Heap = <alpha>[ref,Field alpha]alpha;

const unique created: Field bool;

function {:inline} read<alpha>(H:Heap, r:ref, f:Field alpha): alpha { H[r, f] }
function {:inline} update<alpha>(H:Heap, r:ref, f:Field alpha, v:alpha): Heap { H[r,f := v] }
function anon(heap: Heap, s: Set ref, aheap: Heap) : Heap;

function $IsGoodHeap(Heap): bool;
function {:inline} $IsCreated(H:Heap, r:ref): bool { H[r, created] }

axiom (forall<alpha> heap, aheap: Heap, s: Set ref, o: ref, f: Field alpha :: { read(anon(heap,s,aheap), o, f) }  
           read(anon(heap,s,aheap), o, f) ==
              (if s[o] || !$IsCreated(heap, o)
               then read(aheap, o, f)
               else read(heap, o, f)));

axiom (forall heap, aheap: Heap, r: ref, s: Set ref :: { $IsCreated(anon(heap, s, aheap), r) }
  $IsCreated(heap, r) ==> $IsCreated(anon(heap,s,aheap), r));

function $FreshObjects(Heap): Set ref;
axiom (forall heap: Heap, o: ref :: { $FreshObjects(heap)[o] }
  $FreshObjects(heap)[o] == (!$IsCreated(heap, o)));

//D function $IsHeapAnchor(Heap): bool;
//D var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

// The following is used as a reference heap in places where the translation needs a heap
// but the expression generated is really one that is (at least in a correct program)
// independent of the heap.
//D const $OneHeap: Heap;
//D axiom $IsGoodHeap($OneHeap);
//D
//D function $HeapSucc(Heap, Heap): bool;
//D axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha :: { update(h, r, f, x) }
//D   $IsGoodHeap(update(h, r, f, x)) ==>
//D   $HeapSucc(h, update(h, r, f, x)));
//D axiom (forall a,b,c: Heap :: { $HeapSucc(a,b), $HeapSucc(b,c) }
//D   $HeapSucc(a,b) && $HeapSucc(b,c) ==> $HeapSucc(a,c));
//D axiom (forall h: Heap, k: Heap :: { $HeapSucc(h,k) }
//D   $HeapSucc(h,k) ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));
//D
//D function $HeapSuccGhost(Heap, Heap): bool;
//D axiom (forall h: Heap, k: Heap :: { $HeapSuccGhost(h,k) }
//D   $HeapSuccGhost(h,k) ==>
//D     $HeapSucc(h,k) &&
//D     (forall<alpha> o: ref, f: Field alpha :: { read(k, o, f) }
//D       !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));

// ---------------------------------------------------------------
// -- Non-determinism --------------------------------------------
// ---------------------------------------------------------------

//D type TickType;
//D var $Tick: TickType;

// ---------------------------------------------------------------
// -- Useful macros ----------------------------------------------
// ---------------------------------------------------------------

// havoc everything in $Heap, except {this}+rds+nw
//D procedure $YieldHavoc(this: ref, rds: Set Box, nw: Set Box);
//D   modifies $Heap;
//D   ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
//D             $o != null && read(old($Heap), $o, alloc) ==>
//D             $o == this || rds[$Box($o)] || nw[$Box($o)] ==>
//D               read($Heap, $o, $f) == read(old($Heap), $o, $f));
//D   ensures $HeapSucc(old($Heap), $Heap);
//D
//D // havoc everything in $Heap, except rds-modi-{this}
//D procedure $IterHavoc0(this: ref, rds: Set Box, modi: Set Box);
//D   modifies $Heap;
//D   ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
//D             $o != null && read(old($Heap), $o, alloc) ==>
//D             rds[$Box($o)] && !modi[$Box($o)] && $o != this ==>
//D               read($Heap, $o, $f) == read(old($Heap), $o, $f));
//D   ensures $HeapSucc(old($Heap), $Heap);
//D
//D // havoc $Heap at {this}+modi+nw
//D procedure $IterHavoc1(this: ref, modi: Set Box, nw: Set Box);
//D   modifies $Heap;
//D   ensures (forall<alpha> $o: ref, $f: Field alpha :: { read($Heap, $o, $f) }
//D             $o != null && read(old($Heap), $o, alloc) ==>
//D               read($Heap, $o, $f) == read(old($Heap), $o, $f) ||
//D               $o == this || modi[$Box($o)] || nw[$Box($o)]);
//D   ensures $HeapSucc(old($Heap), $Heap);
//D
//D procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field (Set Box))
//D                         returns (s: Set Box);
//D   ensures (forall bx: Box :: { s[bx] } s[bx] <==>
//D               read(newHeap, this, NW)[bx] ||
//D               ($Unbox(bx) != null && !read(prevHeap, $Unbox(bx):ref, alloc) && read(newHeap, $Unbox(bx):ref, alloc)));

// ---------------------------------------------------------------
// -- Axiomatizations --------------------------------------------
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// -- Axiomatization of sets -------------------------------------
// ---------------------------------------------------------------

type Set T = [T]bool;

function Set#Card<T>(Set T): int;
axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

function Set#Empty<T>(): Set T;
axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);
axiom (forall<T> s: Set T :: { Set#Card(s) }
  (Set#Card(s) == 0 <==> s == Set#Empty()) &&
  (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

// the empty set could be of anything
//axiom (forall<T> t: Ty :: { $Is(Set#Empty() : [T]bool, TSet(t)) } $Is(Set#Empty() : [T]bool, TSet(t)));

function Set#Singleton<T>(T): Set T;
axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);
axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);

function Set#UnionOne<T>(Set T, T): Set T;
axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a,x)[o] }
  Set#UnionOne(a,x)[o] <==> o == x || a[o]);
axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) }
  Set#UnionOne(a, x)[x]);
axiom (forall<T> a: Set T, x: T, y: T :: { Set#UnionOne(a, x), a[y] }
  a[y] ==> Set#UnionOne(a, x)[y]);
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

function Set#Union<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
  Set#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
  a[y] ==> Set#Union(a, b)[y]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), b[y] }
  b[y] ==> Set#Union(a, b)[y]);
axiom (forall<T> a, b: Set T :: { Set#Union(a, b) }
  Set#Disjoint(a, b) ==>
    Set#Difference(Set#Union(a, b), a) == b &&
    Set#Difference(Set#Union(a, b), b) == a);
// Follows from the general union axiom, but might be still worth including, because disjoint union is a common case:
// axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }
//   Set#Disjoint(a, b) ==>
//     Set#Card(Set#Union(a, b)) == Set#Card(a) + Set#Card(b));

function Set#Intersection<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] }
  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

axiom (forall<T> a, b: Set T :: { Set#Union(Set#Union(a, b), b) }
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Union(a, Set#Union(a, b)) }
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(Set#Intersection(a, b), b) }
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Intersection(a, Set#Intersection(a, b)) }
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));
axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));

function Set#Difference<T>(Set T, Set T): Set T;
axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] }
  Set#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
  b[y] ==> !Set#Difference(a, b)[y] );
axiom (forall<T> a, b: Set T ::
  { Set#Card(Set#Difference(a, b)) }
  Set#Card(Set#Difference(a, b)) + Set#Card(Set#Difference(b, a))
  + Set#Card(Set#Intersection(a, b))
    == Set#Card(Set#Union(a, b)) &&
  Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

function Set#Subset<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
// axiom(forall<T> a: Set T, b: Set T ::
//   { Set#Subset(a,b), Set#Card(a), Set#Card(b) }  // very restrictive trigger
//   Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));


function Set#Equal<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
  Set#Equal(a,b) ==> a == b);

function Set#Disjoint<T>(Set T, Set T): bool;
axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------
// -- Axiomatization of isets -------------------------------------
// ---------------------------------------------------------------

//D type ISet T = [T]bool;
//D
//D function ISet#Empty<T>(): Set T;
//D axiom (forall<T> o: T :: { ISet#Empty()[o] } !ISet#Empty()[o]);
//D
//D // the empty set could be of anything
//D //axiom (forall<T> t: Ty :: { $Is(ISet#Empty() : [T]bool, TISet(t)) } $Is(ISet#Empty() : [T]bool, TISet(t)));
//D
//D
//D function ISet#UnionOne<T>(ISet T, T): ISet T;
//D axiom (forall<T> a: ISet T, x: T, o: T :: { ISet#UnionOne(a,x)[o] }
//D   ISet#UnionOne(a,x)[o] <==> o == x || a[o]);
//D axiom (forall<T> a: ISet T, x: T :: { ISet#UnionOne(a, x) }
//D   ISet#UnionOne(a, x)[x]);
//D axiom (forall<T> a: ISet T, x: T, y: T :: { ISet#UnionOne(a, x), a[y] }
//D   a[y] ==> ISet#UnionOne(a, x)[y]);
//D
//D function ISet#Union<T>(ISet T, ISet T): ISet T;
//D axiom (forall<T> a: ISet T, b: ISet T, o: T :: { ISet#Union(a,b)[o] }
//D   ISet#Union(a,b)[o] <==> a[o] || b[o]);
//D axiom (forall<T> a, b: ISet T, y: T :: { ISet#Union(a, b), a[y] }
//D   a[y] ==> ISet#Union(a, b)[y]);
//D axiom (forall<T> a, b: Set T, y: T :: { ISet#Union(a, b), b[y] }
//D   b[y] ==> ISet#Union(a, b)[y]);
//D axiom (forall<T> a, b: ISet T :: { ISet#Union(a, b) }
//D   ISet#Disjoint(a, b) ==>
//D     ISet#Difference(ISet#Union(a, b), a) == b &&
//D     ISet#Difference(ISet#Union(a, b), b) == a);
//D // Follows from the general union axiom, but might be still worth including, because disjoint union is a common case:
//D // axiom (forall<T> a, b: ISet T :: { ISet#Card(ISet#Union(a, b)) }
//D //   ISet#Disjoint(a, b) ==>
//D //     ISet#Card(ISet#Union(a, b)) == ISet#Card(a) + ISet#Card(b));
//D
//D function ISet#Intersection<T>(ISet T, ISet T): ISet T;
//D axiom (forall<T> a: ISet T, b: ISet T, o: T :: { ISet#Intersection(a,b)[o] }
//D   ISet#Intersection(a,b)[o] <==> a[o] && b[o]);
//D
//D axiom (forall<T> a, b: ISet T :: { ISet#Union(ISet#Union(a, b), b) }
//D   ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));
//D axiom (forall<T> a, b: Set T :: { ISet#Union(a, ISet#Union(a, b)) }
//D   ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));
//D axiom (forall<T> a, b: ISet T :: { ISet#Intersection(ISet#Intersection(a, b), b) }
//D   ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));
//D axiom (forall<T> a, b: ISet T :: { ISet#Intersection(a, ISet#Intersection(a, b)) }
//D   ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));
//D
//D
//D function ISet#Difference<T>(ISet T, ISet T): ISet T;
//D axiom (forall<T> a: ISet T, b: ISet T, o: T :: { ISet#Difference(a,b)[o] }
//D   ISet#Difference(a,b)[o] <==> a[o] && !b[o]);
//D axiom (forall<T> a, b: ISet T, y: T :: { ISet#Difference(a, b), b[y] }
//D   b[y] ==> !ISet#Difference(a, b)[y] );
//D
//D function ISet#Subset<T>(ISet T, ISet T): bool;
//D axiom(forall<T> a: ISet T, b: ISet T :: { ISet#Subset(a,b) }
//D   ISet#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
//D // axiom(forall<T> a: ISet T, b: ISet T ::
//D //   { ISet#Subset(a,b), ISet#Card(a), ISet#Card(b) }  // very restrictive trigger
//D //   ISet#Subset(a,b) ==> ISet#Card(a) <= ISet#Card(b));
//D
//D
//D function ISet#Equal<T>(ISet T, ISet T): bool;
//D axiom(forall<T> a: ISet T, b: ISet T :: { ISet#Equal(a,b) }
//D   ISet#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
//D axiom(forall<T> a: ISet T, b: ISet T :: { ISet#Equal(a,b) }  // extensionality axiom for sets
//D   ISet#Equal(a,b) ==> a == b);
//D
//D function ISet#Disjoint<T>(ISet T, ISet T): bool;
//D axiom (forall<T> a: ISet T, b: ISet T :: { ISet#Disjoint(a,b) }
//D   ISet#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

// ---------------------------------------------------------------
// -- Axiomatization of multisets --------------------------------
// ---------------------------------------------------------------

function Math#min(a: int, b: int): int;
axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);
axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);
axiom (forall a: int, b: int :: { Math#min(a, b) } Math#min(a, b) == a || Math#min(a, b) == b);

function Math#clip(a: int): int;
axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);
axiom (forall a: int :: { Math#clip(a) } a < 0  ==> Math#clip(a) == 0);

type MultiSet T = [T]int;

function $IsGoodMultiSet<T>(ms: MultiSet T): bool;
// ints are non-negative, used after havocing, and for conversion from sequences to multisets.
axiom (forall<T> ms: MultiSet T :: { $IsGoodMultiSet(ms) }
  $IsGoodMultiSet(ms) <==>
  (forall bx: T :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

function MultiSet#Card<T>(MultiSet T): int;
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
axiom (forall<T> s: MultiSet T, x: T, n: int :: { MultiSet#Card(s[x := n]) }
  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);

function MultiSet#Empty<T>(): MultiSet T;
axiom (forall<T> o: T :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);
axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) }
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
  (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));

function MultiSet#Singleton<T>(T): MultiSet T;
axiom (forall<T> r: T, o: T :: { MultiSet#Singleton(r)[o] } (MultiSet#Singleton(r)[o] == 1 <==> r == o) &&
                                                            (MultiSet#Singleton(r)[o] == 0 <==> r != o));
axiom (forall<T> r: T :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

function MultiSet#UnionOne<T>(MultiSet T, T): MultiSet T;
// pure containment axiom (in the original multiset or is the added element)
axiom (forall<T> a: MultiSet T, x: T, o: T :: { MultiSet#UnionOne(a,x)[o] }
  0 < MultiSet#UnionOne(a,x)[o] <==> o == x || 0 < a[o]);
// union-ing increases count by one
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#UnionOne(a, x) }
  MultiSet#UnionOne(a, x)[x] == a[x] + 1);
// non-decreasing
axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
  0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);
// other elements unchanged
axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
  x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);
axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#Card(MultiSet#UnionOne(a, x)) }
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);


function MultiSet#Union<T>(MultiSet T, MultiSet T): MultiSet T;
// union-ing is the sum of the contents
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Union(a,b)[o] }
  MultiSet#Union(a,b)[o] == a[o] + b[o]);
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Card(MultiSet#Union(a,b)) }
  MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));

function MultiSet#Intersection<T>(MultiSet T, MultiSet T): MultiSet T;
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Intersection(a,b)[o] }
  MultiSet#Intersection(a,b)[o] == Math#min(a[o],  b[o]));

// left and right pseudo-idempotence
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
  MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
  MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));

// multiset difference, a - b. clip() makes it positive.
function MultiSet#Difference<T>(MultiSet T, MultiSet T): MultiSet T;
axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Difference(a,b)[o] }
  MultiSet#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Difference(a, b), b[y], a[y] }
  a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0 );
axiom (forall<T> a, b: MultiSet T ::
  { MultiSet#Card(MultiSet#Difference(a, b)) }
  MultiSet#Card(MultiSet#Difference(a, b)) + MultiSet#Card(MultiSet#Difference(b, a))
  + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
    == MultiSet#Card(MultiSet#Union(a, b)) &&
  MultiSet#Card(MultiSet#Difference(a, b)) == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

// multiset subset means a must have at most as many of each element as b
function MultiSet#Subset<T>(MultiSet T, MultiSet T): bool;
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Subset(a,b) }
  MultiSet#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <= b[o]));

function MultiSet#Equal<T>(MultiSet T, MultiSet T): bool;
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == b[o]));
// extensionality axiom for multisets
axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
  MultiSet#Equal(a,b) ==> a == b);

function MultiSet#Disjoint<T>(MultiSet T, MultiSet T): bool;
axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Disjoint(a,b) }
  MultiSet#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));

// conversion to a multiset. each element in the original set has duplicity 1.
function MultiSet#FromSet<T>(Set T): MultiSet T;
axiom (forall<T> s: Set T, a: T :: { MultiSet#FromSet(s)[a] }
  (MultiSet#FromSet(s)[a] == 0 <==> !s[a]) &&
  (MultiSet#FromSet(s)[a] == 1 <==> s[a]));
axiom (forall<T> s: Set T :: { MultiSet#Card(MultiSet#FromSet(s)) }
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

// conversion to a multiset, from a sequence.
function MultiSet#FromSeq<T>(Seq T): MultiSet T;
// conversion produces a good map.
axiom (forall<T> s: Seq T :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)) );
// cardinality axiom
axiom (forall<T> s: Seq T ::
  { MultiSet#Card(MultiSet#FromSeq(s)) }
    MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));
// building axiom
axiom (forall<T> s: Seq T, v: T ::
  { MultiSet#FromSeq(Seq#Build(s, v)) }
    MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v)
  );
axiom (forall<T> :: MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);

// concatenation axiom
axiom (forall<T> a: Seq T, b: Seq T ::
  { MultiSet#FromSeq(Seq#Append(a, b)) }
    MultiSet#FromSeq(Seq#Append(a, b)) == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)) );

// update axiom
axiom (forall<T> s: Seq T, i: int, v: T, x: T ::
  { MultiSet#FromSeq(Seq#Update(s, i, v))[x] }
    0 <= i && i < Seq#Length(s) ==>
    MultiSet#FromSeq(Seq#Update(s, i, v))[x] ==
      MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s,i))), MultiSet#Singleton(v))[x] );
  // i.e. MS(Update(s, i, v)) == MS(s) - {{s[i]}} + {{v}}
axiom (forall<T> s: Seq T, x: T :: { MultiSet#FromSeq(s)[x] }
  (exists i : int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && x == Seq#Index(s,i)) <==> 0 < MultiSet#FromSeq(s)[x] );

// ---------------------------------------------------------------
// -- Axiomatization of sequences --------------------------------
// ---------------------------------------------------------------

type Seq T;

function Seq#Length<T>(Seq T): int;
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>(): Seq T;
axiom (forall<T> :: { Seq#Empty(): Seq T } Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) }
  (Seq#Length(s) == 0 ==> s == Seq#Empty())
// The following would be a nice fact to include, because it would enable verifying the
// GenericPick.SeqPick* methods in Test/dafny0/SmallTests.dfy.  However, it substantially
// slows down performance on some other tests, including running seemingly forever on
// some.
//  && (Seq#Length(s) != 0 ==> (exists x: T :: Seq#Contains(s, x)))
  );

// The empty sequence $Is any type
//D axiom (forall<T> t: Ty :: {$Is(Seq#Empty(): Seq T, t)} $Is(Seq#Empty(): Seq T, t));

function Seq#Singleton<T>(T): Seq T;
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, val: T): Seq T;
function Seq#Build_inv0<T>(s: Seq T) : Seq T;
function Seq#Build_inv1<T>(s: Seq T) : T;
axiom (forall<T> s: Seq T, val: T ::
  { Seq#Build(s, val) }
  Seq#Build_inv0(Seq#Build(s, val)) == s &&
  Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall<T> s: Seq T, v: T ::
  { Seq#Build(s,v) }
  Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
  (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));

// Build preserves $Is
//D axiom (forall s: Seq Box, bx: Box, t: Ty :: { $Is(Seq#Build(s,bx),TSeq(t)) }
//D     $Is(s,TSeq(t)) && $IsBox(bx,t) ==> $Is(Seq#Build(s,bx),TSeq(t)));

function Seq#Append<T>(Seq T, Seq T): Seq T;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

// Append preserves $Is
//D axiom (forall s0 : Seq Box, s1 : Seq Box, t : Ty :: { $Is(Seq#Append(s0,s1),t) }
//D     $Is(s0,t) && $Is(s1,t) ==> $Is(Seq#Append(s0,s1),t));

function Seq#Index<T>(Seq T, int): T;
axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

function Seq#Update<T>(Seq T, int, T): Seq T;
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
  0 <= n && n < Seq#Length(s) ==>
    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));

function Seq#Contains<T>(Seq T, T): bool;
axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
  Seq#Contains(s,x) <==>
    (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
axiom (forall<T> x: T ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));

axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) }
  Seq#Contains(Seq#Append(s0, s1), x) <==>
    Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall<T> s: Seq T, v: T, x: T ::  // needed to prove things like '4 in [2,3,4]', see method TestSequences0 in SmallTests.dfy
  { Seq#Contains(Seq#Build(s, v), x) }
    Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));

axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x) <==>
    (exists i: int :: { Seq#Index(s, i) }
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T): bool;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);

function Seq#SameUntil<T>(Seq T, Seq T, int): bool;
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
  Seq#SameUntil(s0,s1,n) <==>
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n);
axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25}
  { Seq#Index(Seq#Take(s,n), j) }
  { Seq#Index(s, j), Seq#Take(s,n) }
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n);
axiom (forall<T> s: Seq T, n: int, j: int ::
  {:weight 25}
  { Seq#Index(Seq#Drop(s,n), j) }
  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
axiom (forall<T> s: Seq T, n: int, k: int ::
  {:weight 25}
  { Seq#Index(s, k), Seq#Drop(s,n) }
  0 <= n && n <= k && k < Seq#Length(s) ==>
    Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));

axiom (forall<T> s, t: Seq T, n: int ::
  { Seq#Take(Seq#Append(s, t), n) }
  { Seq#Drop(Seq#Append(s, t), n) }
  n == Seq#Length(s)
  ==>
  Seq#Take(Seq#Append(s, t), n) == s &&
  Seq#Drop(Seq#Append(s, t), n) == t);

//D function Seq#FromArray(h: Heap, a: ref): Seq Box;
//D axiom (forall h: Heap, a: ref ::
//D   { Seq#Length(Seq#FromArray(h,a)) }
//D   Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));
//D axiom (forall h: Heap, a: ref ::
//D   { Seq#FromArray(h, a) }
//D   (forall i: int ::
//D     // it's important to include both triggers, so that assertions about the
//D     // the relation between the array and the sequence can be proved in either
//D     // direction
//D     { read(h, a, IndexField(i)) }
//D     { Seq#Index(Seq#FromArray(h, a): Seq Box, i) }
//D     0 <= i &&
//D     i < Seq#Length(Seq#FromArray(h, a))  // this will trigger the previous axiom to get a connection with _System.array.Length(a)
//D     ==>
//D     Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));
//D axiom (forall h0, h1: Heap, a: ref ::
//D   { Seq#FromArray(h1, a), $HeapSucc(h0, h1) }
//D   $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) &&
//D   (forall i: int ::
//D     0 <= i && i < _System.array.Length(a) ==> read(h0, a, IndexField(i)) == read(h1, a, IndexField(i)))
//D   ==>
//D   Seq#FromArray(h0, a) == Seq#FromArray(h1, a));
//D axiom (forall h: Heap, i: int, v: Box, a: ref ::
//D   { Seq#FromArray(update(h, a, IndexField(i), v), a) }
//D     0 <= i && i < _System.array.Length(a) ==> Seq#FromArray(update(h, a, IndexField(i), v), a) == Seq#Update(Seq#FromArray(h, a), i, v) );

function Seq#FromArray<T>(h: Heap, a: ref): Seq T;

axiom (forall<T> h: Heap, a: ref ::
  { Seq#Length(Seq#FromArray(h,a): Seq T) }
  Seq#Length(Seq#FromArray(h, a): Seq T) == _System.array.Length(a));
  
axiom (forall<T> h: Heap, a: ref ::
  { Seq#FromArray(h, a): Seq T }
  (forall i: int ::
    // it's important to include both triggers, so that assertions about the
    // the relation between the array and the sequence can be proved in either
    // direction
    { read(h, a, IndexField(i)): T }
    { Seq#Index(Seq#FromArray(h, a): Seq T, i) }
    0 <= i &&
    i < Seq#Length(Seq#FromArray(h, a): Seq T)  // this will trigger the previous axiom to get a connection with _System.array.Length(a)
    ==>
    Seq#Index(Seq#FromArray(h, a): Seq T, i) == read(h, a, IndexField(i))));

// axiom (forall h0, h1: Heap, a: ref ::
//   { Seq#FromArray(h1, a), $HeapSucc(h0, h1) }
//   $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) &&
//   (forall i: int ::
//     0 <= i && i < _System.array.Length(a) ==> read(h0, a, IndexField(i)) == read(h1, a, IndexField(i)))
//   ==>
//   Seq#FromArray(h0, a) == Seq#FromArray(h1, a));
// axiom (forall h: Heap, i: int, v: Box, a: ref ::
//   { Seq#FromArray(update(h, a, IndexField(i), v), a) }
//    0 <= i && i < _System.array.Length(a) ==> Seq#FromArray(update(h, a, IndexField(i), v), a) == Seq#Update(Seq#FromArray(h, a), i, v) );


// Commutability of Take and Drop with Update.
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
// Extension axiom, triggers only on Takes from arrays.
//D axiom (forall h: Heap, a: ref, n0, n1: int ::
//D         { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) }
//D         n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a) ==> Seq#Take(Seq#FromArray(h, a), n1) == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field Box)) );

// drop commutes with build.
axiom (forall<T> s: Seq T, v: T, n: int ::
        { Seq#Drop(Seq#Build(s, v), n) }
        0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );

//D function Seq#Rank<T>(Seq T): int;
//D axiom (forall s: Seq Box, i: int ::
//D         { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) }
//D         0 <= i && i < Seq#Length(s) ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s) );
//D 
//D axiom (forall<T> s: Seq T, i: int ::
//D         { Seq#Rank(Seq#Drop(s, i)) }
//D         0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s) );
//D axiom (forall<T> s: Seq T, i: int ::
//D         { Seq#Rank(Seq#Take(s, i)) }
//D         0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s) );
//D axiom (forall<T> s: Seq T, i: int, j: int ::
//D         { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) }
//D         0 <= i && i < j && j <= Seq#Length(s) ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s) );

// Additional axioms about common things
axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) }
        n == 0 ==> Seq#Drop(s, n) == s);
axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) }
        n == 0 ==> Seq#Take(s, n) == Seq#Empty());
axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) }
        0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
        Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));

// ---------------------------------------------------------------
// -- Axiomatization of Maps -------------------------------------
// ---------------------------------------------------------------

//D type Map U V;
//D
//D // A Map is defined by three functions, Map#Domain, Map#Elements, and #Map#Card.
//D
//D function Map#Domain<U,V>(Map U V) : Set U;
//D
//D function Map#Elements<U,V>(Map U V) : [U]V;
//D
//D function Map#Card<U,V>(Map U V) : int;
//D
//D axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));
//D
//D // The set of Keys of a Map are available by Map#Domain, and the cardinality of that
//D // set is given by Map#Card.
//D
//D axiom (forall<U,V> m: Map U V :: { Set#Card(Map#Domain(m)) }
//D   Set#Card(Map#Domain(m)) == Map#Card(m));
//D
//D // The set of Values of a Map can be obtained by the function Map#Values, which is
//D // defined as follows.  Remember, a Set is defined by membership (using Boogie's
//D // square brackets) and Map#Card, so we need to define what these mean for the Set
//D // returned by Map#Values.
//D
//D function Map#Values<U,V>(Map U V) : Set V;
//D
//D axiom (forall<U,V> m: Map U V, v: V :: { Map#Values(m)[v] }
//D   Map#Values(m)[v] ==
//D 	(exists u: U :: { Map#Domain(m)[u] } { Map#Elements(m)[u] }
//D 	  Map#Domain(m)[u] &&
//D     v == Map#Elements(m)[u]));
//D
//D // The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
//D // function Map#Items.  Again, we need to define membership of Set#Card for this
//D // set.  Everywhere else in this axiomatization, Map is parameterized by types U V,
//D // even though Dafny only ever instantiates U V with Box Box.  This makes the
//D // axiomatization more generic.  Function Map#Items, however, returns a set of
//D // pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
//D // definition of Map#Items here is to be considered Dafny specific.  Also, note
//D // that it relies on the two destructors for 2-tuples.
//D
//D function Map#Items<U,V>(Map U V) : Set Box;
//D
//D function _System.__tuple_h2._0(DatatypeType) : Box;
//D
//D function _System.__tuple_h2._1(DatatypeType) : Box;
//D
//D axiom (forall<U,V> m: Map U V :: { Set#Card(Map#Items(m)) }
//D   Set#Card(Map#Items(m)) == Map#Card(m));
//D
//D axiom (forall m: Map Box Box, item: Box :: { Map#Items(m)[item] }
//D   Map#Items(m)[item] <==>
//D     Map#Domain(m)[_System.__tuple_h2._0($Unbox(item))] &&
//D     Map#Elements(m)[_System.__tuple_h2._0($Unbox(item))] == _System.__tuple_h2._1($Unbox(item)));
//D
//D // Here are the operations that produce Map values.
//D
//D function Map#Empty<U, V>(): Map U V;
//D axiom (forall<U, V> u: U ::
//D         { Map#Domain(Map#Empty(): Map U V)[u] }
//D         !Map#Domain(Map#Empty(): Map U V)[u]);
//D axiom (forall<U, V> m: Map U V :: { Map#Card(m) }
//D  (Map#Card(m) == 0 <==> m == Map#Empty()) &&
//D  (Map#Card(m) != 0 ==> (exists x: U :: Map#Domain(m)[x])));
//D
//D function Map#Glue<U, V>([U] bool, [U]V, Ty): Map U V;
//D axiom (forall<U, V> a: [U] bool, b:[U]V, t:Ty ::
//D         { Map#Domain(Map#Glue(a, b, t)) }
//D         Map#Domain(Map#Glue(a, b, t)) == a);
//D axiom (forall<U, V> a: [U] bool, b:[U]V, t:Ty ::
//D         { Map#Elements(Map#Glue(a, b, t)) }
//D         Map#Elements(Map#Glue(a, b, t)) == b);
//D axiom (forall<U, V> a: [U] bool, b:[U]V, t:Ty ::
//D         { $Is(Map#Glue(a, b, t), t) }
//D         $Is(Map#Glue(a, b, t), t));
//D
//D
//D //Build is used in displays, and for map updates
//D function Map#Build<U, V>(Map U V, U, V): Map U V;
//D /*axiom (forall<U, V> m: Map U V, u: U, v: V ::
//D   { Map#Domain(Map#Build(m, u, v))[u] } { Map#Elements(Map#Build(m, u, v))[u] }
//D   Map#Domain(Map#Build(m, u, v))[u] && Map#Elements(Map#Build(m, u, v))[u] == v);*/
//D
//D axiom (forall<U, V> m: Map U V, u: U, u': U, v: V ::
//D   { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] }
//D   (u' == u ==> Map#Domain(Map#Build(m, u, v))[u'] &&
//D                Map#Elements(Map#Build(m, u, v))[u'] == v) &&
//D   (u' != u ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u'] &&
//D                Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));
//D axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
//D   Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));
//D axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
//D   !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);
//D
//D //equality for maps
//D function Map#Equal<U, V>(Map U V, Map U V): bool;
//D axiom (forall<U, V> m: Map U V, m': Map U V::
//D   { Map#Equal(m, m') }
//D     Map#Equal(m, m') <==> (forall u : U :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
//D                           (forall u : U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));
//D // extensionality
//D axiom (forall<U, V> m: Map U V, m': Map U V::
//D   { Map#Equal(m, m') }
//D     Map#Equal(m, m') ==> m == m');
//D
//D function Map#Disjoint<U, V>(Map U V, Map U V): bool;
//D axiom (forall<U, V> m: Map U V, m': Map U V ::
//D   { Map#Disjoint(m, m') }
//D     Map#Disjoint(m, m') <==> (forall o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));

// ---------------------------------------------------------------
// -- Axiomatization of IMaps ------------------------------------
// ---------------------------------------------------------------

//D type IMap U V;
//D
//D // A IMap is defined by two functions, Map#Domain and Map#Elements.
//D
//D function IMap#Domain<U,V>(IMap U V) : Set U;
//D
//D function IMap#Elements<U,V>(IMap U V) : [U]V;
//D
//D // The set of Values of a IMap can be obtained by the function IMap#Values, which is
//D // defined as follows.  Remember, a ISet is defined by membership (using Boogie's
//D // square brackets) so we need to define what these mean for the Set
//D // returned by Map#Values.
//D
//D function IMap#Values<U,V>(IMap U V) : Set V;
//D
//D axiom (forall<U,V> m: IMap U V, v: V :: { IMap#Values(m)[v] }
//D   IMap#Values(m)[v] ==
//D 	(exists u: U :: { IMap#Domain(m)[u] } { IMap#Elements(m)[u] }
//D 	  IMap#Domain(m)[u] &&
//D     v == IMap#Elements(m)[u]));
//D
//D // The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
//D // function IMap#Items.
//D // Everywhere else in this axiomatization, IMap is parameterized by types U V,
//D // even though Dafny only ever instantiates U V with Box Box.  This makes the
//D // axiomatization more generic.  Function IMap#Items, however, returns a set of
//D // pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
//D // definition of IMap#Items here is to be considered Dafny specific.  Also, note
//D // that it relies on the two destructors for 2-tuples.
//D
//D function IMap#Items<U,V>(IMap U V) : Set Box;
//D
//D axiom (forall m: IMap Box Box, item: Box :: { IMap#Items(m)[item] }
//D   IMap#Items(m)[item] <==>
//D     IMap#Domain(m)[_System.__tuple_h2._0($Unbox(item))] &&
//D     IMap#Elements(m)[_System.__tuple_h2._0($Unbox(item))] == _System.__tuple_h2._1($Unbox(item)));
//D
//D // Here are the operations that produce Map values.
//D function IMap#Empty<U, V>(): IMap U V;
//D axiom (forall<U, V> u: U ::
//D         { IMap#Domain(IMap#Empty(): IMap U V)[u] }
//D         !IMap#Domain(IMap#Empty(): IMap U V)[u]);
//D
//D function IMap#Glue<U, V>([U] bool, [U]V, Ty): IMap U V;
//D axiom (forall<U, V> a: [U] bool, b:[U]V, t:Ty ::
//D         { IMap#Domain(IMap#Glue(a, b, t)) }
//D         IMap#Domain(IMap#Glue(a, b, t)) == a);
//D axiom (forall<U, V> a: [U] bool, b:[U]V, t:Ty ::
//D         { IMap#Elements(IMap#Glue(a, b, t)) }
//D         IMap#Elements(IMap#Glue(a, b, t)) == b);
//D axiom (forall<U, V> a: [U] bool, b:[U]V, t:Ty ::
//D         { $Is(IMap#Glue(a, b, t), t) }
//D         $Is(IMap#Glue(a, b, t), t));
//D
//D //Build is used in displays
//D function IMap#Build<U, V>(IMap U V, U, V): IMap U V;
//D /*axiom (forall<U, V> m: IMap U V, u: U, v: V ::
//D   { IMap#Domain(IMap#Build(m, u, v))[u] } { IMap#Elements(IMap#Build(m, u, v))[u] }
//D   IMap#Domain(IMap#Build(m, u, v))[u] && IMap#Elements(IMap#Build(m, u, v))[u] == v);*/
//D
//D axiom (forall<U, V> m: IMap U V, u: U, u': U, v: V ::
//D   { IMap#Domain(IMap#Build(m, u, v))[u'] } { IMap#Elements(IMap#Build(m, u, v))[u'] }
//D   (u' == u ==> IMap#Domain(IMap#Build(m, u, v))[u'] &&
//D                IMap#Elements(IMap#Build(m, u, v))[u'] == v) &&
//D   (u' != u ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u'] &&
//D                IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));
//D
//D //equality for imaps
//D function IMap#Equal<U, V>(IMap U V, IMap U V): bool;
//D axiom (forall<U, V> m: IMap U V, m': IMap U V::
//D   { IMap#Equal(m, m') }
//D     IMap#Equal(m, m') <==> (forall u : U :: IMap#Domain(m)[u] == IMap#Domain(m')[u]) &&
//D                           (forall u : U :: IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));
//D // extensionality
//D axiom (forall<U, V> m: IMap U V, m': IMap U V::
//D   { IMap#Equal(m, m') }
//D     IMap#Equal(m, m') ==> m == m');

// -------------------------------------------------------------------------
// -- Provide arithmetic wrappers to improve triggering and non-linear math
// -------------------------------------------------------------------------

function INTERNAL_add_boogie(x:int, y:int) : int { x + y }
function INTERNAL_sub_boogie(x:int, y:int) : int { x - y }
function INTERNAL_mul_boogie(x:int, y:int) : int { x * y }
function INTERNAL_div_boogie(x:int, y:int) : int { x div y }
function INTERNAL_mod_boogie(x:int, y:int) : int { x mod y }
function {:never_pattern true} INTERNAL_lt_boogie(x:int, y:int) : bool { x < y }
function {:never_pattern true} INTERNAL_le_boogie(x:int, y:int) : bool { x <= y }
function {:never_pattern true} INTERNAL_gt_boogie(x:int, y:int) : bool { x > y }
function {:never_pattern true} INTERNAL_ge_boogie(x:int, y:int) : bool { x >= y }

function Mul(x, y: int): int { x * y }
function Div(x, y: int): int { x div y }
function Mod(x, y: int): int { x mod y }
function Add(x, y: int): int { x + y }
function Sub(x, y: int): int { x - y }

#if ARITH_DISTR
axiom (forall x, y, z: int ::
  { Mul(Add(x, y), z) }
  Mul(Add(x, y), z) == Add(Mul(x, z), Mul(y, z)));
axiom (forall x,y,z: int ::
  { Mul(x, Add(y, z)) }
  Mul(x, Add(y, z)) == Add(Mul(x, y), Mul(x, z)));
//axiom (forall x, y, z: int ::
//  { Mul(Sub(x, y), z) }
//  Mul(Sub(x, y), z) == Sub(Mul(x, z), Mul(y, z)));
#endif
#if ARITH_MUL_DIV_MOD
axiom (forall x, y: int ::
  { Div(x, y), Mod(x, y) }
  { Mul(Div(x, y), y) }
  y != 0 ==>
  Mul(Div(x, y), y) + Mod(x, y) == x);
#endif
#if ARITH_MUL_SIGN
axiom (forall x, y: int ::
  { Mul(x, y) }
  ((0 <= x && 0 <= y) || (x <= 0 && y <= 0) ==> 0 <= Mul(x, y)));
#endif
#if ARITH_MUL_COMM
axiom (forall x, y: int ::
  { Mul(x, y) }
  Mul(x, y) == Mul(y, x));
#endif
#if ARITH_MUL_ASSOC
axiom (forall x, y, z: int ::
  { Mul(x, Mul(y, z)) }
  Mul(x, Mul(y, z)) == mul(mul(x, y), z));
#endif

// -------------------------------------------------------------------------
// END OF PRELUDE

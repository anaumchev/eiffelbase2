// Automatically generated (01/21/2022 12:39:25.184 PM)

// File: /root/es_ap/trunk/research/extension/autoproof/library/base/mml/set.bpl

// Finite sets.
// (Originally from Dafny Prelude: Copyright (c) Microsoft)

// Set type
type Set T = [T]bool;

// Cardinality
function Set#Card<T>(Set T): int;
axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

// Empty set
function Set#Empty<T>(): Set T;
axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);
axiom (forall<T> s: Set T :: { Set#Card(s) }
  (Set#Card(s) == 0 <==> s == Set#Empty()));// &&
  // (Set#Card(s) != 0 ==> (exists x: T :: s[x])));
axiom (forall<T> f: Field (Set T) :: { Default(f) } Default(f) == Set#Empty() : Set T);  

// Singleton set  
function Set#Singleton<T>(T): Set T;
axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);
axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);
axiom (forall<T> s: Set T, x: T :: { Set#Singleton(x), Set#Card(s) } Set#Card(s) == 1 && s[x]  ==>  s == Set#Singleton(x));

// Is a set empty?
function {: inline } Set#IsEmpty<T>(s: Set T): bool
{ Set#Equal(s, Set#Empty()) }

// An arbitrary element of a nonempty set
function Set#AnyItem<T>(Set T): T;
axiom (forall<T> s: Set T :: { Set#AnyItem(s) } 
  !Set#IsEmpty(s) ==> s[Set#AnyItem(s)]);
  
// Are two sets equal?  
function Set#Equal<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
  Set#Equal(a,b) ==> a == b);  
  
// Is a subset of b?
function Set#Subset<T>(Set T, Set T): bool;
axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b), Set#Card(a) }{ Set#Subset(a,b), Set#Card(b) }
  Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));
  
  
// Is a superset of b?
function {: inline } Set#Superset<T>(a: Set T, b: Set T): bool
{ Set#Subset(b, a) }

// Are a and b disjoint?
function Set#Disjoint<T>(Set T, Set T): bool;
axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));
  
// Set extended with one element  
function Set#Extended<T>(Set T, T): Set T;
axiom (forall<T> a: Set T, x: T, o: T :: { Set#Extended(a,x)[o] }
  Set#Extended(a,x)[o] <==> o == x || a[o]);
axiom (forall<T> a: Set T, x: T :: { Set#Extended(a, x) }
  Set#Extended(a, x)[x]);
axiom (forall<T> a: Set T, x: T, y: T :: { Set#Extended(a, x), a[y] }
  a[y] ==> Set#Extended(a, x)[y]);
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#Extended(a, x)) }
  a[x] ==> Set#Card(Set#Extended(a, x)) == Set#Card(a));  
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#Extended(a, x)) }
  !a[x] ==> Set#Card(Set#Extended(a, x)) == Set#Card(a) + 1);    
  
// Set with one element removed
function Set#Removed<T>(Set T, T): Set T;
axiom (forall<T> a: Set T, x: T, o: T :: { Set#Removed(a,x)[o] }
  Set#Removed(a,x)[o] <==> o != x && a[o]);
axiom (forall<T> a: Set T, x: T :: { Set#Removed(a, x) }
  !Set#Removed(a, x)[x]);
// axiom (forall<T> a: Set T, x: T, y: T :: { Set#Removed(a, x), a[y] }
  // Set#Removed(a, x)[y] ==> a[y]);
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#Removed(a, x)) }
  a[x] ==> Set#Card(Set#Removed(a, x)) == Set#Card(a) - 1);  
axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#Removed(a, x)) }
  !a[x] ==> Set#Card(Set#Removed(a, x)) == Set#Card(a));

// Union of two sets
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

// Intersection of two sets    
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

// Set a with all elements from b removed
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
axiom (forall<T> a: Set T :: { Set#Difference(a,Set#Empty()) }
  Set#Equal(Set#Difference(a,Set#Empty()), a));

// Symmetric difference of two sets  
function Set#SymDifference<T>(a: Set T, b: Set T): Set T
{ Set#Union(Set#Difference(a, b), Set#Difference(b, a)) }


function Set#Min<T>(Set T): T;
axiom (forall s: Set int :: { Set#Min(s) } 
  !Set#IsEmpty(s) ==> s[Set#Min(s)] && (forall x: int :: s[x] ==> x >= Set#Min(s)));

function Set#Max<T>(Set T): T;
axiom (forall s: Set int :: { Set#Max(s) } 
  !Set#IsEmpty(s) ==> s[Set#Max(s)] && (forall x: int :: s[x] ==> x <= Set#Max(s)));
  
function Set#NonNull(s: Set ref): bool
{ (forall x: ref :: { s[x] } s[x] ==> x != Void) }
  
// Type property
function {: inline } Set#ItemsType(heap: HeapType, s: Set ref, t: Type): bool 
{ (forall o: ref :: { s[o] } s[o] ==> detachable(heap, o, t)) }
    
// Integer intervals
type Interval = Set int;

// Interval [l, u]
function Interval#FromRange(int, int): Interval;
axiom (forall l, u: int :: { Set#Card(Interval#FromRange(l, u)) }
  (u < l ==> Set#Card(Interval#FromRange(l, u)) == 0) &&
  (l <= u ==> Set#Card(Interval#FromRange(l, u)) == u - l + 1));
axiom (forall l, u, x: int :: { Interval#FromRange(l, u)[x] }
  Interval#FromRange(l, u)[x] <==> l <= x && x <= u);  

// File: /root/es_ap/trunk/research/extension/autoproof/library/base/mml/sequence.bpl

// Finite sequences.
// (Originally from Dafny Prelude: Copyright (c) Microsoft)

// Sequence type
type Seq T;

// Sequence length
function Seq#Length<T>(Seq T): int;
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

// Empty sequence
function Seq#Empty<T>(): Seq T;
axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());
axiom (forall<T> f: Field (Seq T) :: { Default(f) } Default(f) == Seq#Empty() : Seq T);

// Singleton sequence
function Seq#Singleton<T>(T): Seq T;
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

// Constant sequence
function Seq#Constant<T>(T, int): Seq T;
axiom (forall<T> t: T, n: int :: { Seq#Length(Seq#Constant(t, n)) } 
  n >= 0 ==> Seq#Length(Seq#Constant(t, n)) == n);
axiom (forall<T> t: T, n: int, i: int :: { Seq#Item(Seq#Constant(t, n), i) } 
  1 <= i && i <= n ==> Seq#Item(Seq#Constant(t, n), i) == t);
  

// Does a sequence contain a given element?
function Seq#Has<T>(s: Seq T, x: T): bool;
axiom (forall<T> s: Seq T, x: T :: { Seq#Has(s,x) }
  Seq#Has(s,x) <==>
    (exists i: int :: { Seq#Item(s,i) } 1 <= i && i <= Seq#Length(s) && Seq#Item(s,i) == x));
// axiom (forall<T> s: Seq T, i: int :: { Seq#Item(s, i) }
  // 1 <= i && i <= Seq#Length(s) ==>
    // Seq#Has(s, Seq#Item(s, i)));    
axiom (forall<T> x: T ::
  { Seq#Has(Seq#Empty(), x) }
  !Seq#Has(Seq#Empty(), x));
axiom (forall<T> x, y: T ::
  { Seq#Has(Seq#Singleton(y), x) }
  Seq#Has(Seq#Singleton(y), x) <==> x == y);  
axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Has(Seq#Concat(s0, s1), x) }
  Seq#Has(Seq#Concat(s0, s1), x) <==>
    Seq#Has(s0, x) || Seq#Has(s1, x));
axiom (forall<T> s: Seq T, v: T, x: T ::
  { Seq#Has(Seq#Extended(s, v), x) }
    Seq#Has(Seq#Extended(s, v), x) <==> (v == x || Seq#Has(s, x)));
axiom (forall<T> s: Seq T, v: T, x: T ::
  { Seq#Has(Seq#Prepended(s, v), x) }
    Seq#Has(Seq#Prepended(s, v), x) <==> (v == x || Seq#Has(s, x)));    
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Has(Seq#Take(s, n), x) }
  Seq#Has(Seq#Take(s, n), x) <==>
    (exists i: int :: { Seq#Item(s, i) }
      1 <= i && i <= n && i <= Seq#Length(s) && Seq#Item(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Has(Seq#Drop(s, n), x) }
  Seq#Has(Seq#Drop(s, n), x) <==>
    (exists i: int :: { Seq#Item(s, i) }
      0 <= n && n + 1 <= i && i <= Seq#Length(s) && Seq#Item(s, i) == x));
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Has(Seq#RemovedAt(s, n), x) }
  Seq#Has(Seq#RemovedAt(s, n), x) <==>
    (exists i: int :: { Seq#Item(s, i) }
      1 <= n && n <= Seq#Length(s) && n != i && Seq#Item(s, i) == x));
      
// Is a sequence empty?
function {: inline } Seq#IsEmpty<T>(a: Seq T): bool
{ Seq#Equal(a, Seq#Empty()) }

function Seq#IsConstant<T>(s: Seq T, x: T): bool
{ (forall i: int :: { Seq#Item(s, i) } 1 <= i && i <= Seq#Length(s) ==> Seq#Item(s, i) == x) }

// Element at a given index
function Seq#Item<T>(Seq T, int): T;
axiom (forall<T> t: T :: { Seq#Item(Seq#Singleton(t), 1) } Seq#Item(Seq#Singleton(t), 1) == t);
// axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Item(Seq#Concat(s0,s1), n) }
  // (n <= Seq#Length(s0) ==> Seq#Item(Seq#Concat(s0,s1), n) == Seq#Item(s0, n)) &&
  // (Seq#Length(s0) < n ==> Seq#Item(Seq#Concat(s0,s1), n) == Seq#Item(s1, n - Seq#Length(s0))));
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Item(Seq#Concat(s0,s1), n) }
  Seq#Item(Seq#Concat(s0,s1), n) == if n <= Seq#Length(s0) then Seq#Item(s0, n) else Seq#Item(s1, n - Seq#Length(s0)));  
  
// Set of indexes
function Seq#Domain<T>(q: Seq T): Set int
{ Interval#FromRange(1, Seq#Length(q)) }

// Set of values
function Seq#Range<T>(Seq T): Set T;
axiom (forall<T> q: Seq T, o: T :: { Seq#Range(q)[o] } Seq#Has(q, o) <==> Seq#Range(q)[o]);
axiom (forall<T> s: Seq T :: { Seq#Range(s) }
  (forall i: int :: 1 <= i && i <= Seq#Length(s) ==> Seq#Range(s)[Seq#Item(s, i)]));
// axiom (forall<T> s: Seq T, i: int :: { Seq#Range(s), Seq#Item(s, i) }
  // 1 <= i && i <= Seq#Length(s) ==> Seq#Range(s)[Seq#Item(s, i)]);
  
  
// How many times does x occur in a?
function Seq#Occurrences<T>(Seq T, T): int;
axiom (forall<T> x: T :: {Seq#Occurrences(Seq#Empty(), x)} Seq#Occurrences(Seq#Empty(), x) == 0);
axiom (forall<T> a: Seq T, x: T:: {Seq#Occurrences(Seq#Extended(a, x), x)}
  Seq#Occurrences(Seq#Extended(a, x), x) == Seq#Occurrences(a, x) + 1);
axiom (forall<T> a: Seq T, x: T, y: T :: {Seq#Occurrences(Seq#Extended(a, y), x)}
  x != y ==> Seq#Occurrences(Seq#Extended(a, y), x) == Seq#Occurrences(a, x));
// axiom (forall<T> x: T:: {Seq#Occurrences(Seq#Singleton(x), x)}
  // Seq#Occurrences(Seq#Singleton(x), x) == 1);
// axiom (forall<T> x: T, y: T :: {Seq#Occurrences(Seq#Singleton(x), y)}
  // x != y ==> Seq#Occurrences(Seq#Singleton(x), y) == 0);  
 // axiom (forall<T> a: Seq T, x: T :: {Seq#Occurrences(a, x)}
  // !Seq#Has(a, x) ==> Seq#Occurrences(a, x) == 0);
  
function Seq#IndexOf<T>(Seq T, T): int;
axiom (forall<T> s: Seq T, x: T :: { Seq#IndexOf(s,x) }
  Seq#Has(s,x) ==> 1 <= Seq#IndexOf(s,x) && Seq#IndexOf(s,x) <= Seq#Length(s) && Seq#Item(s, Seq#IndexOf(s,x)) == x);
axiom (forall<T> s: Seq T, x: T :: { Seq#IndexOf(s,x) }
  !Seq#Has(s,x) ==> Seq#IndexOf(s,x) < 1 || Seq#Length(s) < Seq#IndexOf(s,x));

// Are two sequences equal?  
function Seq#Equal<T>(Seq T, Seq T): bool;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) <==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Item(s0,j) } { Seq#Item(s1,j) }
        1 <= j && j <= Seq#Length(s0) ==> Seq#Item(s0,j) == Seq#Item(s1,j)));
axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);
  
// Is q0 a prefix of q1?  
function {: inline } Seq#Prefix<T>(q0: Seq T, q1: Seq T): bool
{ Seq#Equal(q0, Seq#Take(q1, Seq#Length(q0))) }

// Is |q0| <= |q1|?
function {: inline } Seq#LessEqual<T>(q0: Seq T, q1: Seq T): bool
{ Seq#Length(q0) <= Seq#Length(q1) }

// Prefix of length how_many
function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
  // (n < 0 ==> Seq#Length(Seq#Take(s,n)) == 0) &&
  // (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
  // (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));  
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Item(Seq#Take(s,n), j) } {:weight 25}
  1 <= j && j <= n && j <= Seq#Length(s) ==>
    Seq#Item(Seq#Take(s,n), j) == Seq#Item(s, j));
// axiom (forall<T> s: Seq T, n: int :: {Seq#Take(s,n)}
  // (n < 0 ==> Seq#Take(s,n) == Seq#Empty() : Seq T) &&
  // (n >= Seq#Length(s) ==> Seq#Take(s,n) == s));

// Sequence without its prefix of length howMany    
function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  // (n < 0 ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s)) &&
  // (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
  // (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Item(Seq#Drop(s,n), j) } {:weight 25}
  0 <= n && 1 <= j && j <= Seq#Length(s)-n ==> 
    Seq#Item(Seq#Drop(s,n), j) == Seq#Item(s, j+n));
// axiom (forall<T> s: Seq T, n: int :: {Seq#Drop(s,n)}
  // (n < 0 ==> Seq#Drop(s,n) == s) &&
  // (n >= Seq#Length(s) ==> Seq#Drop(s,n) == Seq#Empty() : Seq T));  

// First element
function {: inline } Seq#First<T>(q: Seq T): T
{ Seq#Item(q, 1) } 

// Last element
function {: inline } Seq#Last<T>(q: Seq T): T
{ Seq#Item(q, Seq#Length(q)) } 

// Sequence with the first element removed
function {: inline } Seq#ButFirst<T>(q: Seq T): Seq T
{ Seq#Drop(q, 1) } 

// Sequence with the last element removed
function {: inline } Seq#ButLast<T>(q: Seq T): Seq T
{ Seq#Take(q, Seq#Length(q) - 1) } 

// Prefix until upper
function Seq#Front<T>(q: Seq T, upper: int): Seq T
// { Seq#Take(q, upper) }
{ if 0 <= upper then Seq#Take(q, upper) else Seq#Empty() : Seq T } 
axiom (forall<T> q: Seq T :: { Seq#Front(q, Seq#Length(q)) } Seq#Front(q, Seq#Length(q)) == q);

// Suffix from lower
function Seq#Tail<T>(q: Seq T, lower: int): Seq T
// { Seq#Drop(q, lower - 1) }
{ if 1 <= lower then Seq#Drop(q, lower - 1) else q } 
axiom (forall<T> q: Seq T :: { Seq#Tail(q, 1) } Seq#Tail(q, 1) == q);

// Subsequence from lower to upper
function Seq#Interval<T>(q: Seq T, lower: int, upper: int): Seq T
{ Seq#Tail(Seq#Front(q, upper), lower) }

// Sequence with element at position i removed
// function {: inline } Seq#RemovedAt<T>(q: Seq T, i: int): Seq T
// { Seq#Concat(Seq#Take(q, i - 1), Seq#Drop(q, i)) } 
function Seq#RemovedAt<T>(q: Seq T, i: int): Seq T;
axiom (forall<T> q: Seq T, i: int :: { Seq#Length(Seq#RemovedAt(q, i)) }
	Seq#Length(Seq#RemovedAt(q, i)) == Seq#Length(q) - 1);
axiom (forall<T> q: Seq T, i: int, j: int :: { Seq#Item(Seq#RemovedAt(q, i), j) }
	(j < i ==> Seq#Item(Seq#RemovedAt(q, i), j) == Seq#Item(q, j)) &&
	(i <= j ==> Seq#Item(Seq#RemovedAt(q, i), j) == Seq#Item(q, j + 1)));

// Sequence extended with x at the end
function Seq#Extended<T>(s: Seq T, val: T): Seq T;
axiom (forall<T> s: Seq T, v: T :: { Seq#Length(Seq#Extended(s,v)) }
  Seq#Length(Seq#Extended(s,v)) == 1 + Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Item(Seq#Extended(s,v), i) }
  (i == Seq#Length(s) + 1 ==> Seq#Item(Seq#Extended(s,v), i) == v) &&
  (i <= Seq#Length(s) ==> Seq#Item(Seq#Extended(s,v), i) == Seq#Item(s, i)));
  
// Sequence with x inserted at position i
function {: inline } Seq#ExtendedAt<T>(s: Seq T, i: int, val: T): Seq T
{
  Seq#Concat (Seq#Extended(Seq#Take(s, i - 1), val), Seq#Drop(s, i - 1))
}
axiom (forall<T> s: Seq T, i: int, val: T :: { Seq#Length(Seq#ExtendedAt(s, i, val)) }
	Seq#Length(Seq#ExtendedAt(s, i, val)) == Seq#Length(s) + 1);

// Sequence prepended with x at the beginning
function Seq#Prepended<T>(s: Seq T, val: T): Seq T;
// {
  // Seq#Concat (Seq#Singleton(val), s)
// }
axiom (forall<T> s: Seq T, v: T :: { Seq#Length(Seq#Prepended(s, v)) }
	Seq#Length(Seq#Prepended(s, v)) == Seq#Length(s) + 1);    
axiom (forall<T> s: Seq T, v: T, i: int :: { Seq#Item(Seq#Prepended(s, v), i) }
  (2 <= i && i <= Seq#Length(s) + 1 ==> Seq#Item(Seq#Prepended(s, v), i) == Seq#Item(s, i - 1)) &&
  (i == 1 ==> Seq#Item(Seq#Prepended(s, v), 1) == v));
  
// Concatenation of two sequences
function Seq#Concat<T>(Seq T, Seq T): Seq T;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Concat(s0,s1)) }
  Seq#Length(Seq#Concat(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

// Sequence with x at position i.
function Seq#Update<T>(Seq T, int, T): Seq T;
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
  1 <= i && i <= Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Item(Seq#Update(s,i,v),n) }
  1 <= n && n <= Seq#Length(s) ==>
    (i == n ==> Seq#Item(Seq#Update(s,i,v),n) == v) &&
    (i != n ==> Seq#Item(Seq#Update(s,i,v),n) == Seq#Item(s,n)));
    
// Sequence converted to a bag
function Seq#ToBag<T>(Seq T): Bag T;
axiom (forall<T> s: Seq T :: { Seq#ToBag(s) } Bag#IsValid(Seq#ToBag(s)));
// building axiom
axiom (forall<T> s: Seq T, v: T ::
  { Seq#ToBag(Seq#Extended(s, v)) }
    Seq#ToBag(Seq#Extended(s, v)) == Bag#Extended(Seq#ToBag(s), v)
  );
axiom (forall<T> :: Seq#ToBag(Seq#Empty(): Seq T) == Bag#Empty(): Bag T);
axiom (forall<T> s: Seq T :: { Bag#Card(Seq#ToBag(s)) }
  Bag#Card(Seq#ToBag(s)) == Seq#Length(s));

// concatenation axiom
axiom (forall<T> a: Seq T, b: Seq T, x: T ::
  { Seq#ToBag(Seq#Concat(a, b))[x] }
    Seq#ToBag(Seq#Concat(a, b))[x] == Seq#ToBag(a)[x] + Seq#ToBag(b)[x] );
    
// update axiom
axiom (forall<T> s: Seq T, i: int, v: T, x: T ::
  { Seq#ToBag(Seq#Update(s, i, v))[x] }
    1 <= i && i <= Seq#Length(s) ==>
    Seq#ToBag(Seq#Update(s, i, v))[x] ==
      Bag#Extended(Bag#Difference(Seq#ToBag(s), Bag#Singleton(Seq#Item(s,i))), v)[x] );
  // i.e. MS(Update(s, i, v)) == MS(s) - {{s[i]}} + {{v}}
axiom (forall<T> s: Seq T, x: T :: { Seq#ToBag(s)[x] } Seq#Has(s, x) <==> 0 < Seq#ToBag(s)[x]);
axiom (forall<T> s: Seq T, x: T :: { Seq#ToBag(s)[x] } Seq#ToBag(s)[x] == Seq#Occurrences(s, x));

// removed axiom
axiom (forall<T> s: Seq T, i: int :: { Seq#ToBag(Seq#RemovedAt(s, i)) }
  1 <= i && i <= Seq#Length(s) ==> Seq#ToBag(Seq#RemovedAt(s, i)) == Bag#Difference(Seq#ToBag(s), Bag#Singleton(Seq#Item(s,i))));
// prepend axiom
axiom (forall<T> s: Seq T, v: T :: { Seq#ToBag(Seq#Prepended(s, v)) }
  Seq#ToBag(Seq#Prepended(s, v)) == Bag#Extended(Seq#ToBag(s), v));

// Sequence converted to map
function Seq#ToMap<T>(Seq T): Map int T;
axiom (forall<T> s: Seq T :: { Map#Equal(Seq#ToMap(s), Map#Empty()) }
  Map#Equal(Seq#ToMap(s), Map#Empty()) <==> Seq#Equal (s, Seq#Empty() : Seq T));
axiom (forall<T> s: Seq T :: { Map#Domain(Seq#ToMap(s)) }
  Map#Domain(Seq#ToMap(s)) == Seq#Domain(s));
axiom (forall<T> s: Seq T :: { Map#Card(Seq#ToMap(s)) }
  Map#Card(Seq#ToMap(s)) == Seq#Length(s));
axiom (forall<T> s: Seq T, i: int :: { Map#Item(Seq#ToMap(s), i) }
  1 <= i && i <= Seq#Length(s) ==> Map#Item(Seq#ToMap(s), i) == Seq#Item(s, i));  
  
axiom (forall<T> s: Seq T :: { Map#ToBag(Seq#ToMap(s)) }
  Bag#Equal(Map#ToBag(Seq#ToMap(s)), Seq#ToBag(s)));  
  

// Additional axioms about common things
    
// axiom (forall<T> s, t: Seq T ::
  // { Seq#Concat(s, t) }
  // Seq#Take(Seq#Concat(s, t), Seq#Length(s)) == s &&
  // Seq#Drop(Seq#Concat(s, t), Seq#Length(s)) == t);
  

// Commutability of Take and Drop with Update.
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Take(Seq#Update(s, i, v), n) }
    1 <= i && i <= n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Take(Seq#Update(s, i, v), n) }
    n < i && i <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Drop(Seq#Update(s, i, v), n) }
    0 <= n && n + 1 <= i && i <= Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
  { Seq#Drop(Seq#Update(s, i, v), n) }
    1 <= i && i <= n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
// drop commutes with build.
axiom (forall<T> s: Seq T, v: T, n: int ::
  { Seq#Drop(Seq#Extended(s, v), n) }
    0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Extended(s, v), n) == Seq#Extended(Seq#Drop(s, n), v) );

axiom (forall<T> :: Seq#Take(Seq#Empty() : Seq T, 0) == Seq#Empty() : Seq T);  // [][..0] == []
axiom (forall<T> :: Seq#Drop(Seq#Empty() : Seq T, 0) == Seq#Empty() : Seq T);  // [][0..] == []

// 2 x Take and drop
// axiom (forall<T> s: Seq T, n: int, m: int :: { Seq#Take(Seq#Take(s, n), m) }
	// (n <= m ==> Seq#Equal(Seq#Take(Seq#Take(s, n), m), Seq#Take(s, n))) &&
	// (n >= m ==> Seq#Equal(Seq#Take(Seq#Take(s, n), m), Seq#Take(s, m))));
// axiom (forall<T> s: Seq T, n: int, m: int :: { Seq#Drop(Seq#Drop(s, n), m) }
	// Seq#Equal(Seq#Drop(Seq#Drop(s, n), m), Seq#Drop(s, n + m)));

function Seq#NonNull(s: Seq ref): bool
{ (forall i: int :: { Seq#Item(s, i) } 1 <= i && i <= Seq#Length(s) ==> Seq#Item(s, i) != Void) }

function Seq#NoDuplicates<T>(s: Seq T): bool
{ (forall i, j: int :: { Seq#Item(s, i), Seq#Item(s, j) } 1 <= i && i < j && j <= Seq#Length(s) ==> Seq#Item(s, i) != Seq#Item(s, j)) }
// { (forall i, j: int :: 1 <= i && i <= Seq#Length(s) && 1 <= j && j <= ) }

// Type property
function {: inline } Seq#ItemsType(heap: HeapType, s: Seq ref, t: Type): bool 
{ (forall i: int :: { Seq#Item(s, i) } 1 <= i && i <= Seq#Length(s) ==> detachable(heap, Seq#Item(s, i), t)) }

// function Seq#IsSorted<T>(s: Seq T) returns (bool);

//axiom (forall s: Seq int, i: int ::
//    1 <= i && i < Seq#Length(s) && Seq#IsSorted(s) ==> Seq#Item(s, i) <= Seq#Item(s, i+1));
// axiom (forall s: Seq int ::
  // { Seq#IsSorted(s) }
    // Seq#IsSorted(s) ==> (forall i, j: int :: 1 <= i && i <= Seq#Length(s) && i <= j && j <= Seq#Length(s) ==> Seq#Item(s, i) <= Seq#Item(s, j)));
// axiom (forall s: Seq int ::
  // { Seq#IsSorted(s) }
    // Seq#Length(s) <= 1 ==> Seq#IsSorted(s));
// axiom (forall s: Seq int, i: int ::
    // 1 <= i && i < Seq#Length(s) && Seq#IsSorted(Seq#Front(s, i)) && Seq#Item(s, i) <= Seq#Item(s, i+1) ==> Seq#IsSorted(Seq#Front(s, i+1)));

// axiom (forall s: Seq int ::
  // { Seq#Range(s) }
    // (forall i: int, j: int ::
		// 1 <= i && i < Seq#Length(s) && 1 <= j && j < Seq#Length(s) ==>
			// Seq#Range(Seq#Update(Seq#Update(s, i, Seq#Item(s, j)), j, Seq#Item(s, i))) == Seq#Range(s)));





// File: /root/es_ap/trunk/research/extension/autoproof/library/base/mml/map.bpl

// Finite maps.
// (Originally from Dafny Prelude: Copyright (c) Microsoft)

// Map type
type Map U V;

// Map domain
function Map#Domain<U, V>(Map U V): Set U;

// Mapping from keys to values
function Map#Elements<U, V>(Map U V): [U]V;

// // Map constructed from domain and elements
// function Map#Glue<U, V>([U] bool, [U]V): Map U V;
// axiom (forall<U, V> a: [U] bool, b:[U]V ::
  // { Map#Domain(Map#Glue(a, b)) }
    // Map#Domain(Map#Glue(a, b)) == a);
// axiom (forall<U, V> a: [U] bool, b:[U]V ::
  // { Map#Elements(Map#Glue(a, b)) }
    // Map#Elements(Map#Glue(a, b)) == b);

// Map cardinality
function Map#Card<U, V>(Map U V): int;
axiom (forall<U, V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));     
axiom (forall<U, V> m: Map U V :: { Map#Card(m), Map#Domain(m) } Map#Card(m) == Set#Card(Map#Domain(m)));

// Empty map
function Map#Empty<U, V>(): Map U V;
axiom (forall<U, V> u: U ::
  { Map#Domain(Map#Empty(): Map U V)[u] }
   !Map#Domain(Map#Empty(): Map U V)[u]);
axiom (forall<U, V> m: Map U V :: { Map#Card(m) } Map#Card(m) == 0 <==> m == Map#Empty());
axiom (forall<U, V> f: Field (Map U V) :: { Default(f) } Default(f) == Map#Empty() : Map U V);  

// Singleton map
function {: inline } Map#Singleton<U, V>(k: U, x: V): Map U V
{ Map#Update(Map#Empty(), k, x) }

// Does the map contain value x?
function {: inline } Map#Has<U, V>(m: Map U V, x: V): bool
{ Map#Range(m)[x] }

// Is the map empty?
function {: inline } Map#IsEmpty<U, V>(m: Map U V): bool
{ Map#Equal(m, Map#Empty()) }

// Are all values in m equal to c?
function Map#IsConstant<U, V>(m: Map U V, c: V): bool
{ (forall k: U :: Map#Domain(m)[k] ==> Map#Elements(m)[k] == c) }

// Element at a given key
function {: inline } Map#Item<U, V>(m: Map U V, k: U): V
{ Map#Elements(m)[k] }

// Map Range
function {: inline } Map#Range<U, V>(m: Map U V): Set V
{ Map#Image(m, Map#Domain(m)) }

// Image of a set
function Map#Image<U, V>(m: Map U V, s: Set U): Set V;
axiom (forall<U, V> m: Map U V, s: Set U, x: V :: { Map#Image(m, s)[x] }
  Map#Image(m, s)[x] <==> (exists k: U :: s[k] && Map#Elements(m)[k] == x));
axiom (forall<U, V> m: Map U V, s: Set U, k: U :: { Map#Image(m, s)[Map#Elements(m)[k]] }
  s[k] ==> Map#Image(m, s)[Map#Elements(m)[k]]);

// Image of a sequence  
function Map#SequenceImage<U, V>(m: Map U V, s: Seq U): Seq V;
axiom (forall<U, V> m: Map U V, s: Seq U :: { Seq#Length(Map#SequenceImage(m, s)) } 
  Seq#Length(Map#SequenceImage(m, s)) == Seq#Length(s));
axiom (forall<U, V> m: Map U V, s: Seq U, i: int :: { Seq#Item(Map#SequenceImage(m, s), i) } 
  Seq#Item(Map#SequenceImage(m, s), i) == Map#Elements(m)[Seq#Item(s, i)]);  
  
// Bag of map values  
function Map#ToBag<U, V>(m: Map U V): Bag V;
axiom (forall<U, V> m: Map U V :: { Map#ToBag(m) } Bag#IsValid(Map#ToBag(m)));
// axiom (forall<U, V> m: Map U V :: { Bag#Equal(Map#ToBag(m), Bag#Empty()) } 
  // Bag#Equal(Map#ToBag(m), Bag#Empty() : Bag V) <==> Map#Equal (m, Map#Empty() : Map U V));
axiom (forall<U, V> :: Map#ToBag(Map#Empty() :  Map U V) == Bag#Empty() : Bag V);
axiom (forall<U, V> m: Map U V, x: V :: { Map#ToBag(m)[x] } 
  Map#ToBag(m)[x] > 0 <==> Map#Range(m)[x]);
// update axiom
axiom (forall<U, V> m: Map U V, k: U, x: V :: { Map#ToBag(Map#Update(m, k, x)) }
  !Map#Domain(m)[k] ==> Map#ToBag(Map#Update(m, k, x)) == Bag#Extended(Map#ToBag(m), x));
axiom (forall<U, V> m: Map U V, k: U, x: V :: { Map#ToBag(Map#Update(m, k, x)) }
  Map#Domain(m)[k] ==> Map#ToBag(Map#Update(m, k, x)) == Bag#Extended(Bag#Removed(Map#ToBag(m), Map#Elements(m)[k]), x));
// removed axiom
axiom (forall<U, V> m: Map U V, k: U :: { Map#ToBag(Map#Removed(m, k)) }
  Map#Domain(m)[k] ==> Map#ToBag(Map#Removed(m, k)) == Bag#Removed(Map#ToBag(m), Map#Elements(m)[k]));  
// cardinality axiom 
axiom (forall<U, V> m: Map U V :: { Bag#Card(Map#ToBag(m)) }
  Bag#Card(Map#ToBag(m)) == Map#Card(m));  
// disjoint union axiom
axiom (forall<U, V> a: Map U V, b: Map U V, x: V ::
  { Map#ToBag(Map#Override(a, b))[x] }
    Set#Disjoint(Map#Domain(a), Map#Domain(b)) ==> Map#ToBag(Map#Override(a, b))[x] == Map#ToBag(a)[x] + Map#ToBag(b)[x] );
  
  
// Equality
function Map#Equal<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') <==> (forall u : U :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
                          (forall u : U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));
// extensionality
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') ==> m == m');

// Dow two maps have disjoint domains?    
function Map#Disjoint<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V ::
  { Map#Disjoint(m, m') }
    Map#Disjoint(m, m') <==> (forall o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));  
  
// Map with a key-value pair updated
function Map#Update<U, V>(Map U V, U, V): Map U V;
/*axiom (forall<U, V> m: Map U V, u: U, v: V ::
  { Map#Domain(Map#Update(m, u, v))[u] } { Map#Elements(Map#Update(m, u, v))[u] }
  Map#Domain(Map#Update(m, u, v))[u] && Map#Elements(Map#Update(m, u, v))[u] == v);*/
axiom (forall<U, V> m: Map U V, u: U, u': U, v: V ::
  { Map#Domain(Map#Update(m, u, v))[u'] } { Map#Elements(Map#Update(m, u, v))[u'] }
  (u' == u ==> Map#Domain(Map#Update(m, u, v))[u'] &&
               Map#Elements(Map#Update(m, u, v))[u'] == v) &&
  (u' != u ==> Map#Domain(Map#Update(m, u, v))[u'] == Map#Domain(m)[u'] &&
               Map#Elements(Map#Update(m, u, v))[u'] == Map#Elements(m)[u']));
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Update(m, u, v)) }
  Map#Domain(m)[u] ==> Map#Card(Map#Update(m, u, v)) == Map#Card(m));  
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Update(m, u, v)) }
  !Map#Domain(m)[u] ==> Map#Card(Map#Update(m, u, v)) == Map#Card(m) + 1);  
  
// Map with a key removed  
function Map#Removed<U, V>(Map U V, U): Map U V;
axiom (forall<U, V> m: Map U V, k: U :: { Map#Domain(Map#Removed(m, k)) }
  Map#Domain(Map#Removed(m, k)) == Set#Removed(Map#Domain(m), k));
axiom (forall<U, V> m: Map U V, k: U, i: U :: { Map#Elements(Map#Removed(m, k))[i] }
  Map#Elements(Map#Removed(m, k))[i] == Map#Elements(m)[i]);
axiom (forall<U, V> m: Map U V, k: U :: { Map#Domain(m)[k], Map#Removed(m, k) }
  !Map#Domain(m)[k] ==> Map#Removed(m, k) == m);
  
// Map restricted to a subdomain  
function Map#Restricted<U, V>(Map U V, Set U): Map U V;
axiom (forall<U, V> m: Map U V, s: Set U :: { Map#Domain(Map#Restricted(m, s)) }
  Map#Domain(Map#Restricted(m, s)) == Set#Intersection(Map#Domain(m), s));
axiom (forall<U, V> m: Map U V, s: Set U, i: U :: { Map#Elements(Map#Restricted(m, s))[i] }
  Map#Elements(Map#Restricted(m, s))[i] == Map#Elements(m)[i]);
  
// Map override (right-biased union)
function  Map#Override<U, V>(Map U V, Map U V): Map U V;
axiom (forall<U, V> a: Map U V, b: Map U V :: { Map#Domain(Map#Override(a, b)) }
  Map#Domain(Map#Override(a, b)) == Set#Union(Map#Domain(a), Map#Domain(b)));
axiom (forall<U, V> a: Map U V, b: Map U V, i: U :: { Map#Elements(Map#Override(a, b))[i] }
  Map#Elements(Map#Override(a, b))[i] == if Map#Domain(b)[i] then Map#Elements(b)[i] else Map#Elements(a)[i]);  
  
// Inverse
function Map#Inverse<U, V>(Map U V): Rel V U;
axiom (forall<U, V> a: Map U V, u: U, v: V :: { Map#Inverse(a)[v, u] }
  Map#Inverse(a)[v, u] <==> Map#Domain(a)[u] && Map#Elements(a)[u] == v);
axiom (forall<U, V> a: Map U V :: { Rel#Card(Map#Inverse(a)) }
  Rel#Card(Map#Inverse(a)) == Map#Card(a));
axiom (forall<U, V> a: Map U V :: { Rel#Domain(Map#Inverse(a)) }
  Rel#Domain(Map#Inverse(a)) == Map#Range(a));
axiom (forall<U, V> a: Map U V :: { Rel#Range(Map#Inverse(a)) }
  Rel#Range(Map#Inverse(a)) == Map#Domain(a));
  
// Type properties

function {: inline } Map#DomainType<T>(heap: HeapType, m: Map ref T, t: Type): bool 
{ (forall o: ref :: { Map#Domain(m)[o] } Map#Domain(m)[o] ==> detachable(heap, o, t)) }  

function {: inline } Map#RangeType<T>(heap: HeapType, m: Map T ref, t: Type): bool 
{ (forall i: T :: { Map#Domain(m)[i] } Map#Domain(m)[i] ==> detachable(heap, Map#Elements(m)[i], t)) }  

  
  
               
// File: /root/es_ap/trunk/research/extension/autoproof/library/base/mml/relation.bpl

// Finite relation.

// Relation type
type Rel U V = [U, V]bool;

// Domain
function Rel#Domain<U, V>(Rel U V): Set U;
axiom (forall<U, V> r: Rel U V, u: U :: { Rel#Domain(r)[u] }
  Rel#Domain(r)[u] <==> (exists v: V :: r[u, v]));
  
// Range
function Rel#Range<U, V>(Rel U V): Set V;
axiom (forall<U, V> r: Rel U V, v: V :: { Rel#Range(r)[v] }
  Rel#Range(r)[v] <==> (exists u: U :: r[u, v]));  
  
// Conversion to set
function Rel#ToSet<U, V>(Rel U V): Set (Pair U V);
axiom (forall<U, V> r: Rel U V, u: U, v: V :: { r[u, v] }{ Rel#ToSet(r)[Pair#Make(u, v)] } 
  r[u, v] <==> Rel#ToSet(r)[Pair#Make(u, v)]);

// Cardinality
function Rel#Card<U, V>(r: Rel U V): int
{ Set#Card(Rel#ToSet(r)) }
// axiom (forall<U, V> r: Rel U V :: { Rel#Card(r) } 0 <= Rel#Card(r));

// Empty relation
function Rel#Empty<U, V>(): Rel U V;
axiom (forall<U, V> u: U, v: V :: { Rel#Empty()[u, v] } !Rel#Empty()[u, v]);
// axiom (forall<U, V> r: Rel U V :: { Rel#Card(r) }
  // (Rel#Card(r) == 0 <==> r == Rel#Empty()) &&
  // (Rel#Card(r) != 0 ==> (exists u: U, v: V :: r[u, v])));
axiom (forall<U, V> r: Rel U V :: { Rel#Domain(r), Rel#Empty() }{ Set#IsEmpty(Rel#Domain(r)) }
  (Set#IsEmpty(Rel#Domain(r)) <==> r == Rel#Empty()));
axiom (forall<U, V> r: Rel U V :: { Rel#Range(r), Rel#Empty() }{ Set#IsEmpty(Rel#Range(r)) }
  (Set#IsEmpty(Rel#Range(r)) <==> r == Rel#Empty()));  
axiom (forall<U, V> r: Rel U V :: { Rel#ToSet(r) }
  (Set#IsEmpty(Rel#ToSet(r)) <==> r == Rel#Empty()));  
axiom (forall<U, V> f: Field (Rel U V) :: { Default(f) } Default(f) == Rel#Empty() : Rel U V);    

// Singleton relation  
function Rel#Singleton<U, V>(U, V): Rel U V;
// axiom (forall<U, V> u: U, v: V :: { Rel#Singleton(u, v) } Rel#Singleton(u, v)[u, v]);
axiom (forall<U, V> u: U, v: V, x: U, y: V :: { Rel#Singleton(u, v)[x, y] } Rel#Singleton(u, v)[x, y] <==> u == x && v == y);
// axiom (forall<U, V> u: U, v: V :: { Rel#Card(Rel#Singleton(u, v)) } Rel#Card(Rel#Singleton(u, v)) == 1);
// axiom (forall<U, V> u: U, v: V :: { Rel#Domain(Rel#Singleton(u, v)) } 
  // Rel#Domain(Rel#Singleton(u, v)) == Set#Singleton(u));
// axiom (forall<U, V> u: U, v: V :: { Rel#Range(Rel#Singleton(u, v)) } 
  // Rel#Range(Rel#Singleton(u, v)) == Set#Singleton(v));
axiom (forall<U, V> u: U, v: V :: { Rel#ToSet(Rel#Singleton(u, v)) } 
  Rel#ToSet(Rel#Singleton(u, v)) == Set#Singleton(Pair#Make(u, v)));  
  
// Is the relation empty?
function {: inline} Rel#IsEmpty<U, V>(r: Rel U V): bool
{ Rel#Equal(Rel#Empty(), r) }

// Image of a domain element
function Rel#ImageOf<U, V>(r: Rel U V, u: U): Set V;
axiom (forall<U, V> r: Rel U V, u: U, v: V :: { Rel#ImageOf(r, u)[v] }
  Rel#ImageOf(r, u)[v] <==> r[u, v]);
axiom (forall<U, V> r: Rel U V, u: U :: { Rel#ImageOf(r, u) }
  Set#Subset(Rel#ImageOf(r, u), Rel#Range(r)));
  
  
// Image of a set
function Rel#Image<U, V>(r: Rel U V, s: Set U): Set V;
axiom (forall<U, V> r: Rel U V, s: Set U, v: V :: { Rel#Image(r, s)[v] }
  Rel#Image(r, s)[v] <==> (exists u: U :: s[u] && r[u, v]));
axiom (forall<U, V> r: Rel U V, s: Set U :: { Rel#Image(r, s) }
  Set#Subset(Rel#Image(r, s), Rel#Range(r)));  
  
// Are two relation equal?  
function Rel#Equal<U, V>(Rel U V, Rel U V): bool;
axiom(forall<U, V> a: Rel U V, b: Rel U V :: { Rel#Equal(a, b) }
  Rel#Equal(a, b) <==> (forall u: U, v: V :: {a[u, v]} {b[u, v]} a[u, v] <==> b[u, v]));
axiom(forall<U, V> a: Rel U V, b: Rel U V :: { Rel#Equal(a, b), Rel#ToSet(a), Rel#ToSet(b) }
  Rel#Equal(a, b) <==> Set#Equal(Rel#ToSet(a), Rel#ToSet(b)));  
axiom(forall<U, V> a: Rel U V, b: Rel U V :: { Rel#Equal(a, b) }  // extensionality axiom for relation
  Rel#Equal(a, b) ==> a == b);

// Relation extended with one element  
function Rel#Extended<U, V>(Rel U V, U, V): Rel U V;
axiom (forall<U, V> a: Rel U V, u: U, v: V, x: U, y: V :: { Rel#Extended(a, u, v)[x, y] }
  Rel#Extended(a, u, v)[x, y] <==> (u == x && v == y) || a[x, y]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Extended(a, u, v) }
  // Rel#Extended(a, u, v)[u, v]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V, x: U, y: V :: { Rel#Extended(a, u, v), a[x, y] }
  // a[x, y] ==> Rel#Extended(a, u, v)[x, y]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Card(Rel#Extended(a, u, v)) }
  // a[u, v] ==> Rel#Card(Rel#Extended(a, u, v)) == Rel#Card(a));  
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Card(Rel#Extended(a, u, v)) }
  // !a[u, v] ==> Rel#Card(Rel#Extended(a, u, v)) == Rel#Card(a) + 1);
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Domain(Rel#Extended(a, u, v)) }
  // Rel#Domain(Rel#Extended(a, u, v)) == Set#Extended(Rel#Domain(a), u));  
// axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#Range(Rel#Extended(a, u, v)) }
  // Rel#Range(Rel#Extended(a, u, v)) == Set#Extended(Rel#Range(a), v));  
axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#ToSet(Rel#Extended(a, u, v)) }
  Rel#ToSet(Rel#Extended(a, u, v)) == Set#Extended(Rel#ToSet(a), Pair#Make(u, v)));  
  
  
// Relation with one element removed
function Rel#Removed<U, V>(Rel U V, U, V): Rel U V;
axiom (forall<U, V> a: Rel U V, u: U, v: V, x: U, y: V :: { Rel#Removed(a, u, v)[x, y] }
  Rel#Removed(a, u, v)[x, y] <==> (u != x || v != y) && a[x, y]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V  :: { Rel#Removed(a, u, v) }
  // !Rel#Removed(a, u, v)[u, v]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V, x: U, y: V :: { Rel#Removed(a, u, v), a[x, y] }
  // Rel#Removed(a, u, v)[x, y] ==> a[x, y]);
// axiom (forall<U, V> a: Rel U V, u: U, v: V  :: { Rel#Card(Rel#Removed(a, u, v)) }
  // a[u, v] ==> Rel#Card(Rel#Removed(a, u, v)) == Rel#Card(a) - 1);  
// axiom (forall<U, V> a: Rel U V, u: U, v: V  :: { Rel#Card(Rel#Removed(a, u, v)) }
  // !a[u, v] ==> Rel#Card(Rel#Removed(a, u, v)) == Rel#Card(a));
axiom (forall<U, V> a: Rel U V, u: U, v: V :: { Rel#ToSet(Rel#Removed(a, u, v)) }
  Rel#ToSet(Rel#Removed(a, u, v)) == Set#Removed(Rel#ToSet(a), Pair#Make(u, v)));    
  
// Restriction on a subdomain
function Rel#Restricted<U, V>(Rel U V, Set U): Rel U V;  
axiom (forall<U, V> a: Rel U V, s: Set U, x: U, y: V :: { Rel#Restricted(a, s)[x, y] }
  Rel#Restricted(a, s)[x, y] <==> a[x, y] && s[x]);
axiom (forall<U, V> a: Rel U V, s: Set U :: { Rel#Domain(Rel#Restricted(a, s)) }
  Rel#Domain(Rel#Restricted(a, s)) == Set#Intersection(Rel#Domain(a), s));

// Inverse  
function Rel#Inverse<U, V>(Rel U V): Rel V U;
axiom (forall<U, V> a: Rel U V, x: U, y: V :: { Rel#Inverse(a)[y, x] }
  Rel#Inverse(a)[y, x] <==> a[x, y]);
axiom (forall<U, V> a: Rel U V :: { Rel#Card(Rel#Inverse(a)) }
  Rel#Card(Rel#Inverse(a)) == Rel#Card(a));  
axiom (forall<U, V> a: Rel U V :: { Rel#Domain(Rel#Inverse(a)) }
  Rel#Domain(Rel#Inverse(a)) == Rel#Range(a));  
axiom (forall<U, V> a: Rel U V :: { Rel#Range(Rel#Inverse(a)) }
  Rel#Range(Rel#Inverse(a)) == Rel#Domain(a));  
  
// Union of two relations
function Rel#Union<U, V>(Rel U V, Rel U V): Rel U V;
// axiom (forall<U, V> a: Rel U V, b: Rel U V, u: U, v: V :: { Rel#Union(a, b)[u, v] }
  // Rel#Union(a, b)[u, v] <==> a[u, v] || b[u, v]);
// axiom (forall<U, V> a, b: Rel U V, u: U, v: V :: { Rel#Union(a, b), a[u, v] }
  // a[u, v] ==> Rel#Union(a, b)[u, v]);
// axiom (forall<U, V> a, b: Rel U V, u: U, v: V :: { Rel#Union(a, b), b[u, v] }
  // b[u, v] ==> Rel#Union(a, b)[u, v]);
// // axiom (forall<U, V> a, b: Rel U V :: { Rel#Union(a, b) }
  // // Rel#Disjoint(a, b) ==>
    // // Rel#Difference(Rel#Union(a, b), a) == b &&
    // // Rel#Difference(Rel#Union(a, b), b) == a);
axiom (forall<U, V> a, b: Rel U V :: { Rel#ToSet(Rel#Union(a, b)) }
  Rel#ToSet(Rel#Union(a, b)) == Set#Union(Rel#ToSet(a), Rel#ToSet(b)));	

// Intersection of two sets    
function Rel#Intersection<U, V>(Rel U V, Rel U V): Rel U V;
// axiom (forall<U, V> a: Rel U V, b: Rel U V, u: U, v: V :: { Rel#Intersection(a, b)[u, v] }
  // Rel#Intersection(a,b)[u, v] <==> a[u, v] && b[u, v]);
axiom (forall<U, V> a, b: Rel U V :: { Rel#ToSet(Rel#Intersection(a, b)) }
  Rel#ToSet(Rel#Intersection(a, b)) == Set#Intersection(Rel#ToSet(a), Rel#ToSet(b)));	  
  
// axiom (forall<U, V> a, b: Rel U V :: { Rel#Union(Rel#Union(a, b), b) }
  // Rel#Union(Rel#Union(a, b), b) == Rel#Union(a, b));
// axiom (forall<U, V> a, b: Rel U V :: { Rel#Union(a, Rel#Union(a, b)) }
  // Rel#Union(a, Rel#Union(a, b)) == Rel#Union(a, b));
// axiom (forall<U, V> a, b: Rel U V :: { Rel#Intersection(Rel#Intersection(a, b), b) }
  // Rel#Intersection(Rel#Intersection(a, b), b) == Rel#Intersection(a, b));
// axiom (forall<U, V> a, b: Rel U V :: { Rel#Intersection(a, Rel#Intersection(a, b)) }
  // Rel#Intersection(a, Rel#Intersection(a, b)) == Rel#Intersection(a, b));
// axiom (forall<U, V> a, b: Rel U V :: { Rel#Card(Rel#Union(a, b)) }{ Rel#Card(Rel#Intersection(a, b)) }
  // Rel#Card(Rel#Union(a, b)) + Rel#Card(Rel#Intersection(a, b)) == Rel#Card(a) + Rel#Card(b));

// Relation a with all elements from b removed
function Rel#Difference<U, V>(Rel U V, Rel U V): Rel U V;
// axiom (forall<U, V> a: Rel U V, b: Rel U V, u: U, v: V :: { Rel#Difference(a, b)[u, v] }
  // Rel#Difference(a, b)[u, v] <==> a[u, v] && !b[u, v]);
// axiom (forall<U, V> a, b: Rel U V, u: U, v: V :: { Rel#Difference(a, b), b[u, v] }
  // b[u, v] ==> !Rel#Difference(a, b)[u, v]);
// axiom (forall<U, V> a, b: Rel U V ::
  // { Rel#Card(Rel#Difference(a, b)) }
  // Rel#Card(Rel#Difference(a, b)) + Rel#Card(Rel#Difference(b, a)) 
  // + Rel#Card(Rel#Intersection(a, b))
    // == Rel#Card(Rel#Union(a, b)) &&
  // Rel#Card(Rel#Difference(a, b)) == Rel#Card(a) - Rel#Card(Rel#Intersection(a, b)));
// axiom (forall<U, V> a: Rel U V :: { Rel#Difference(a,Rel#Empty()) }
  // Rel#Equal(Rel#Difference(a,Rel#Empty()), a));
axiom (forall<U, V> a, b: Rel U V :: { Rel#ToSet(Rel#Difference(a, b)) }
  Rel#ToSet(Rel#Difference(a, b)) == Set#Difference(Rel#ToSet(a), Rel#ToSet(b)));  

// Symmetric difference of two relations  
function Rel#SymDifference<U, V>(a: Rel U V, b: Rel U V): Rel U V;
// { Rel#Union(Rel#Difference(a, b), Rel#Difference(b, a)) }
axiom (forall<U, V> a, b: Rel U V :: { Rel#ToSet(Rel#SymDifference(a, b)) }
  Rel#ToSet(Rel#SymDifference(a, b)) == Set#SymDifference(Rel#ToSet(a), Rel#ToSet(b)));  

// Type properties

function {: inline } Rel#DomainType<T>(heap: HeapType, r: Rel ref T, t: Type): bool 
{ (forall o: ref :: { Rel#Domain(r)[o] } Rel#Domain(r)[o] ==> detachable(heap, o, t)) }  

function {: inline } Rel#RangeType<T>(heap: HeapType, r: Rel T ref, t: Type): bool 
{ (forall o: ref :: { Rel#Range(r)[o] } Rel#Range(r)[o] ==> detachable(heap, o, t)) }  

// File: /root/es_ap/trunk/research/extension/autoproof/library/base/mml/bag.bpl

// Finite bags.
// (Originally from Dafny Prelude: Copyright (c) Microsoft)

// Bag type
type Bag T = [T]int;

// Bag invariant
function Bag#IsValid<T>(b: Bag T): bool;
// ints are non-negative, used after havocing, and for conversion from sequences to multisets.
axiom (forall<T> b: Bag T :: { Bag#IsValid(b) } 
  Bag#IsValid(b) <==> (forall bx: T :: { b[bx] } 0 <= b[bx]));

// Bag size
function Bag#Card<T>(Bag T): int;
axiom (forall<T> s: Bag T :: { Bag#Card(s) } 0 <= Bag#Card(s));     
axiom (forall<T> s: Bag T, x: T, n: int :: { Bag#Card(s[x := n]) }
  0 <= n ==> Bag#Card(s[x := n]) == Bag#Card(s) - s[x] + n);

// Empty bag  
function Bag#Empty<T>(): Bag T;
axiom (forall<T> o: T :: { Bag#Empty()[o] } Bag#Empty()[o] == 0);
axiom (forall<T> s: Bag T :: { Bag#Card(s) }
  (Bag#Card(s) == 0 <==> s == Bag#Empty()) &&
  (Bag#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));
axiom (forall<T> f: Field (Bag T) :: { Default(f) } Default(f) == Bag#Empty() : Bag T);  

// Singleton bag
function Bag#Singleton<T>(T): Bag T;
axiom (forall<T> r: T, o: T :: { Bag#Singleton(r)[o] } (Bag#Singleton(r)[o] == 1 <==> r == o) &&
                                                            (Bag#Singleton(r)[o] == 0 <==> r != o));
axiom (forall<T> r: T :: { Bag#Singleton(r) } Bag#Equal(Bag#Singleton(r), Bag#Extended(Bag#Empty(), r)));

// Bag that contains multiple occurrences of the same element
function Bag#Multiple<T>(T, int): Bag T;
axiom (forall<T> r: T, n: int, o: T :: { Bag#Multiple(r, n)[o] } (Bag#Multiple(r, n)[o] == n <==> r == o) &&
                                                            (Bag#Multiple(r, n)[o] == 0 <==> r != o));
axiom (forall<T> r: T, n: int :: { Bag#Multiple(r, n) } Bag#Equal(Bag#Multiple(r, n), Bag#ExtendedMultiple(Bag#Empty(), r, n)));                                                            
            
// Is x contained in b?            
function {: inline } Bag#Has<T>(b: Bag T, x: T): bool
{ b[x] > 0 }                                                            

// Is b empty?
function {: inline } Bag#IsEmpty<T>(b: Bag T): bool
{ Bag#Equal(b, Bag#Empty()) }

// Does b contain each element c times?
function Bag#IsConstant<T>(b: Bag T, c: int): bool
{ (forall o: T :: b[o] != 0 ==> b[o] == c )}

// Set of values contained in the bag
function Bag#Domain<T>(Bag T): Set T;
axiom (forall <T> b: Bag T, o: T :: { Bag#Domain(b)[o] } Bag#Domain(b)[o] <==> b[o] > 0 );
axiom (forall <T> b: Bag T :: { Bag#IsEmpty(b), Bag#Domain(b) }{ Set#IsEmpty(Bag#Domain(b)) } Bag#IsEmpty(b) <==> Set#IsEmpty(Bag#Domain(b)) );

// Do two bags contain the same number of the same elements?
function Bag#Equal<T>(Bag T, Bag T): bool;
axiom(forall<T> a: Bag T, b: Bag T :: { Bag#Equal(a,b) }
  Bag#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == b[o]));
// extensionality axiom for multisets
axiom(forall<T> a: Bag T, b: Bag T :: { Bag#Equal(a,b) }
  Bag#Equal(a,b) ==> a == b);
  
// Does a have at most as many of each element as b?
function Bag#Subset<T>(Bag T, Bag T): bool;
axiom(forall<T> a: Bag T, b: Bag T :: { Bag#Subset(a,b) }
  Bag#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <= b[o]));

// Do two bags have no elements in common?
function Bag#Disjoint<T>(Bag T, Bag T): bool;
axiom (forall<T> a: Bag T, b: Bag T :: { Bag#Disjoint(a,b) }
  Bag#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));
  
// Bag extended with one occurrence of an element
function Bag#Extended<T>(Bag T, T): Bag T;
// pure containment axiom
axiom (forall<T> a: Bag T, x: T, o: T :: { Bag#Extended(a,x)[o] }
  0 < Bag#Extended(a,x)[o] <==> o == x || 0 < a[o]);
// union-ing increases count by one
axiom (forall<T> a: Bag T, x: T :: { Bag#Extended(a, x) }
  Bag#Extended(a, x)[x] == a[x] + 1);
// non-decreasing
axiom (forall<T> a: Bag T, x: T, y: T :: { Bag#Extended(a, x), a[y] }
  0 < a[y] ==> 0 < Bag#Extended(a, x)[y]);
// other elements unchanged
axiom (forall<T> a: Bag T, x: T, y: T :: { Bag#Extended(a, x), a[y] }
  x != y ==> a[y] == Bag#Extended(a, x)[y]);
axiom (forall<T> a: Bag T, x: T :: { Bag#Card(Bag#Extended(a, x)) }
  Bag#Card(Bag#Extended(a, x)) == Bag#Card(a) + 1);    
  
// Bag extended with multiple occurrences of an element
function Bag#ExtendedMultiple<T>(Bag T, T, int): Bag T;
axiom (forall<T> a: Bag T, x: T :: { Bag#ExtendedMultiple(a, x, 0) }
  Bag#Equal(Bag#ExtendedMultiple(a, x, 0), a));
// pure containment axiom
axiom (forall<T> a: Bag T, x: T, n: int, o: T :: { Bag#ExtendedMultiple(a, x, n)[o] }
  n > 0 ==> (0 < Bag#ExtendedMultiple(a, x, n)[o] <==> o == x || 0 < a[o]));
// union-ing increases count by n
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#ExtendedMultiple(a, x, n) }
  Bag#ExtendedMultiple(a, x, n)[x] == a[x] + n);
// non-decreasing
axiom (forall<T> a: Bag T, x: T, n: int, y: T :: { Bag#ExtendedMultiple(a, x, n), a[y] }
  0 < a[y] ==> 0 < Bag#ExtendedMultiple(a, x, n)[y]);
// other elements unchanged
axiom (forall<T> a: Bag T, x: T, n: int, y: T :: { Bag#ExtendedMultiple(a, x, n), a[y] }
  x != y ==> a[y] == Bag#ExtendedMultiple(a, x, n)[y]);
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#Card(Bag#ExtendedMultiple(a, x, n)) }
  Bag#Card(Bag#ExtendedMultiple(a, x, n)) == Bag#Card(a) + n);    
  
// Bag with one occurrence of an element removed
function Bag#Removed<T>(Bag T, T): Bag T;
axiom (forall<T> a: Bag T, x: T :: { Bag#Removed(a, x)[x] }
  a[x] > 0 ==> Bag#Removed(a, x)[x] == a[x] - 1);
axiom (forall<T> a: Bag T, x: T :: { Bag#Removed(a, x)[x] }
  a[x] == 0 ==> Bag#Removed(a, x)[x] == 0);  
axiom (forall<T> a: Bag T, x: T, y: T :: { Bag#Removed(a, x)[y] }
  x != y ==> a[y] == Bag#Removed(a, x)[y]);
axiom (forall<T> a: Bag T, x: T :: { Bag#Card(Bag#Removed(a, x)) }
  a[x] > 0 ==> Bag#Card(Bag#Removed(a, x)) == Bag#Card(a) - 1);    
axiom (forall<T> a: Bag T, x: T :: { Bag#Card(Bag#Removed(a, x)) }
  a[x] == 0 ==> Bag#Card(Bag#Removed(a, x)) == Bag#Card(a));  
  
// Bag with multiple occurrences of an element removed
function Bag#RemovedMultiple<T>(Bag T, T, int): Bag T;
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#RemovedMultiple(a, x, n)[x] }
  a[x] >= n ==> Bag#RemovedMultiple(a, x, n)[x] == a[x] - n);
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#RemovedMultiple(a, x, n)[x] }
  a[x] < n ==> Bag#RemovedMultiple(a, x, n)[x] == 0);  
axiom (forall<T> a: Bag T, x: T, n: int, y: T :: { Bag#RemovedMultiple(a, x, n), a[y] }
  x != y ==> a[y] == Bag#RemovedMultiple(a, x, n)[y]);
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#Card(Bag#RemovedMultiple(a, x, n)) }
  a[x] >= n ==> Bag#Card(Bag#RemovedMultiple(a, x, n)) == Bag#Card(a) - n);    
axiom (forall<T> a: Bag T, x: T, n: int :: { Bag#Card(Bag#RemovedMultiple(a, x, n)) }
  a[x] < 0 ==> Bag#Card(Bag#Removed(a, x)) == Bag#Card(a) - a[x]);  
// special cases  
axiom (forall<T> a: Bag T, x: T :: { Bag#RemovedMultiple(a, x, 0) }
  Bag#Equal(Bag#RemovedMultiple(a, x, 0), a));  
  
  
// Bag with all occurrences of an element removed.  
function Bag#RemovedAll<T>(Bag T, T): Bag T;
axiom (forall<T> a: Bag T, x: T :: { Bag#RemovedAll(a, x)[x] }
  Bag#RemovedAll(a, x)[x] == 0);  
axiom (forall<T> a: Bag T, x: T, y: T :: { Bag#RemovedAll(a, x), a[y] }
  x != y ==> a[y] == Bag#RemovedAll(a, x)[y]);  
axiom (forall<T> a: Bag T, x: T :: {Bag#Card(Bag#RemovedAll(a, x))}
  Bag#Card(Bag#RemovedAll(a, x)) == Bag#Card(a) - a[x]);
  
// Bag that consists only of those elements of a that are in s.  
function Bag#Restricted<T>(Bag T, Set T): Bag T;  
axiom (forall<T> a: Bag T, s: Set T, x: T :: { Bag#Restricted(a, s)[x] }
  Bag#Restricted(a, s)[x] == if s[x] then a[x] else 0);  

// Union of two bags  
function Bag#Union<T>(Bag T, Bag T): Bag T;
// union-ing is the sum of the contents
axiom (forall<T> a: Bag T, b: Bag T, o: T :: { Bag#Union(a,b)[o] }
  Bag#Union(a,b)[o] == a[o] + b[o]);
axiom (forall<T> a: Bag T, b: Bag T :: { Bag#Card(Bag#Union(a,b)) }
  Bag#Card(Bag#Union(a,b)) == Bag#Card(a) + Bag#Card(b));
  
// Intersection of two bags
function Bag#Intersection<T>(Bag T, Bag T): Bag T;
axiom (forall<T> a: Bag T, b: Bag T, o: T :: { Bag#Intersection(a,b)[o] }
  Bag#Intersection(a,b)[o] == min(a[o],  b[o]));
// left and right pseudo-idempotence
axiom (forall<T> a, b: Bag T :: { Bag#Intersection(Bag#Intersection(a, b), b) }
  Bag#Intersection(Bag#Intersection(a, b), b) == Bag#Intersection(a, b));
axiom (forall<T> a, b: Bag T :: { Bag#Intersection(a, Bag#Intersection(a, b)) }
  Bag#Intersection(a, Bag#Intersection(a, b)) == Bag#Intersection(a, b));

// Difference of two multisets
function Bag#Difference<T>(Bag T, Bag T): Bag T;
axiom (forall<T> a: Bag T, b: Bag T, o: T :: { Bag#Difference(a,b)[o] }
  Bag#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
axiom (forall<T> a, b: Bag T, y: T :: { Bag#Difference(a, b), b[y], a[y] }
  a[y] <= b[y] ==> Bag#Difference(a, b)[y] == 0 );
axiom (forall<T> a, b: Bag T ::
  { Bag#Card(Bag#Difference(a, b)) }
  Bag#Card(Bag#Difference(a, b)) + Bag#Card(Bag#Difference(b, a)) 
  + 2 * Bag#Card(Bag#Intersection(a, b))
    == Bag#Card(Bag#Union(a, b)) &&
  Bag#Card(Bag#Difference(a, b)) == Bag#Card(a) - Bag#Card(Bag#Intersection(a, b)));

// Conversion from set
function Bag#FromSet<T>(Set T): Bag T;
axiom (forall<T> s: Set T, a: T :: { Bag#FromSet(s)[a] }
  (Bag#FromSet(s)[a] == 0 <==> !s[a]) &&
  (Bag#FromSet(s)[a] == 1 <==> s[a]));
axiom (forall<T> s: Set T :: { Bag#Card(Bag#FromSet(s)) }
  Bag#Card(Bag#FromSet(s)) == Set#Card(s));  

// Auxiliary functions
  
function Math#clip(a: int): int;
axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);
axiom (forall a: int :: { Math#clip(a) } a < 0  ==> Math#clip(a) == 0);

// Type property
function {: inline } Bag#DomainType(heap: HeapType, b: Bag ref, t: Type): bool 
{ (forall o: ref :: { Bag#Domain(b)[o] }{ b[o] } Bag#Domain(b)[o] ==> detachable(heap, o, t)) }
  
// File: /root/es_ap/trunk/research/extension/autoproof/library/base/mml/pair.bpl

// Pairs.

// Pair type
type Pair G H;

// Constructor
function Pair#Make<G, H>(G, H): Pair G H;
// Left component
function Pair#Left<G, H>(Pair G H): G;
// Right component
function Pair#Right<G, H>(Pair G H): H;

axiom (forall<G, H> x: G, y: H :: { Pair#Left(Pair#Make(x, y)) } Pair#Left(Pair#Make(x, y)) == x);
axiom (forall<G, H> x: G, y: H :: { Pair#Right(Pair#Make(x, y)) } Pair#Right(Pair#Make(x, y)) == y);

// Are two pairs equal?
function Pair#Equal<G, H>(p: Pair G H, q: Pair G H): bool
{ Pair#Left(p) == Pair#Left(q) && Pair#Right(p) == Pair#Right(q) }
axiom(forall<G, H> p: Pair G H, q: Pair G H :: { Pair#Equal(p, q) }  // extensionality axiom for pairs
  Pair#Equal(p, q) ==> p == q);  

// Type properties

function {: inline } Pair#LeftType<T>(heap: HeapType, p: Pair ref T, t: Type): bool 
{ detachable(heap, Pair#Left(p), t) }  

function {: inline } Pair#RightType<T>(heap: HeapType, p: Pair T ref, t: Type): bool 
{ detachable(heap, Pair#Right(p), t) }  

// File: /usr/local/Eiffel_21.11/studio/tools/autoproof/base_theory.bpl

// ----------------------------------------------------------------------
// Reference types

type ref; // Type definition for reference types
const Void: ref; // Constant for Void references

// Is r1 <= r2 in the well-founded order?
function ref_rank_leq(r1, r2: ref): bool
{ r2 == Void ==> r1 == Void }

// ----------------------------------------------------------------------
// Heap and allocation

type Field _; // Type of a field (with open subtype)
// function IsGhostField<alpha>(field: Field alpha): bool; // Is this field a ghost field?
function FieldId<alpha>(field: Field alpha, t: Type): int; // ID of field within t; used to express that all fields of the same class are distinct.

// Default field value
function Default<alpha>(Field alpha): alpha;
axiom (forall f: Field bool :: !Default(f));
axiom (forall f: Field int :: Default(f) == 0);
axiom (forall f: Field ref :: Default(f) == Void);
axiom (forall f: Field real :: Default(f) == 0.0);

type HeapType = <alpha>[ref, Field alpha]alpha; // Type of a heap (with generic field subtype and generic content type)
const allocated: Field bool; // Ghost field for allocation status of objects

// Function which defines basic properties of a heap
function IsHeap(heap: HeapType): bool;

// The global heap (which is always a heap)
var Heap: HeapType where IsHeap(Heap);

// Function that defines properties of two (transitively) successive heaps
function HeapSucc(HeapType, HeapType): bool;
axiom (forall<alpha> h: HeapType, r: ref, f: Field alpha, x: alpha :: { h[r, f := x] }
  IsHeap(h[r, f := x]) ==>
  HeapSucc(h, h[r, f := x]));  
axiom (forall a,b,c: HeapType :: { HeapSucc(a,b), HeapSucc(b,c) }
  HeapSucc(a,b) && HeapSucc(b,c) ==> HeapSucc(a,c));
axiom (forall h: HeapType, k: HeapType :: { HeapSucc(h,k) }
  HeapSucc(h,k) ==> (forall o: ref :: { k[o, allocated] } h[o, allocated] ==> k[o, allocated]));  


// ----------------------------------------------------------------------
// Typing

type Type; // Type definition for Eiffel types
const unique ANY: Type; // Type for ANY
const unique NONE: Type; // Type for NONE

// Type function for objects.
function type_of(o: ref): Type;
function is_frozen(t: Type): bool;

// Typing axioms
axiom (forall t: Type :: { ANY <: t } ANY <: t <==> t == ANY);
axiom (forall t: Type :: t <: ANY); // All types inherit from ANY.
// axiom (forall t: Type :: NONE <: t); // NONE inherits from all types.
// axiom (forall h: HeapType :: IsHeap(h) ==> h[Void, allocated]); // Void is always allocated.
axiom (forall h: HeapType, f: Field ref, o: ref :: IsHeap(h) && h[o, allocated] ==> h[h[o, f], allocated]); // All reference fields are allocated.
axiom (forall r: ref :: (r == Void) <==> (type_of(r) == NONE)); // Void is only reference of type NONE.
// axiom (forall a, b: ref :: (type_of(a) != type_of(b)) ==> (a != b)); // Objects that have different dynamic type cannot be aliased.
// axiom (forall t: Type :: is_frozen(t) ==> (forall t2: Type :: t2 <: t ==> t2 == t || t2 == NONE)); // Only NONE inherits from frozen types.
axiom (forall t: Type, r: ref :: { is_frozen(t), type_of(r) } (r != Void && type_of(r) <: t && is_frozen(t)) ==> (type_of(r) == t)); // Non-void references of a frozen type are exact.
// axiom (forall h: HeapType, t: Type, o: ref :: { is_frozen(t), attached_exact(h, o, t) } IsHeap(h) && is_frozen(t) && attached(h, o, t) ==> attached_exact(h, o, t));

// ----------------------------------------------------------------------
// Built-in attributes

const closed: Field bool; // Ghost field for open/closed status of an object.
const owner: Field ref; // Ghost field for owner of an object.
const owns: Field (Set ref); // Ghost field for owns set of an object.
const observers: Field (Set ref); // Ghost field for observers set of an object.
const subjects: Field (Set ref); // Ghost field for subjects set of an object.

// Analogue of `detachable_attribute' and `set_detachable_attribute' for built-in attributes:
axiom (forall heap: HeapType, o: ref :: { heap[o, owner] } IsHeap(heap) && o != Void && heap[o, allocated] ==> heap[heap[o, owner], allocated]);
axiom (forall heap: HeapType, o, o': ref :: { heap[o, owns][o'] } IsHeap(heap) && o != Void && heap[o, allocated] && heap[o, owns][o'] ==> heap[o', allocated]);
axiom (forall heap: HeapType, o, o': ref :: { heap[o, subjects][o'] } IsHeap(heap) && o != Void && heap[o, allocated] && heap[o, subjects][o'] ==> heap[o', allocated]);
axiom (forall heap: HeapType, o, o': ref :: { heap[o, observers][o'] } IsHeap(heap) && o != Void && heap[o, allocated] && heap[o, observers][o'] ==> heap[o', allocated]);

// Is o open in h? (not closed and free)
function is_open(h: HeapType, o: ref): bool {
	!h[o, closed]
}

// Is o closed in h?
function is_closed(h: HeapType, o: ref): bool {
	h[o, closed]
}

// Is o free? (owner is open)
function {:inline} is_free(h: HeapType, o: ref): bool {
  h[o, owner] == Void
}

// Is o wrapped in h? (closed and free)
function is_wrapped(h: HeapType, o: ref): bool {
	h[o, closed] && is_free(h, o)
}

// Is o' in the ownership domain of o? Yes if they are equal, or both closed and o' is transitively owned by o
function in_domain(h: HeapType, o: ref, o': ref): bool
{
	o == o' || ( h[o, closed] && h[o', closed] && in_domain(h, o, h[o', owner]) )
}

axiom (forall h: HeapType, o, o': ref :: { in_domain(h, o, o') } IsHeap(h) && h[o, closed] && h[o, owns][o'] ==> in_domain(h, o, o'));
axiom (forall h: HeapType, o, o': ref :: { in_domain(h, o, o'), trans_owns(h, o) } IsHeap(h) && h[o, closed] ==> (in_trans_owns(h, o, o') <==> in_domain(h, o, o')));
axiom (forall h: HeapType, o, o': ref :: { in_domain(h, o, o') } IsHeap(h) && o != o' && Set#Equal(Set#Empty(), h[o, owns]) ==> !in_domain(h, o, o'));
axiom (forall h: HeapType, o, o', o'': ref :: { in_domain(h, o, o'), Set#Equal(Set#Singleton(o''), h[o, owns]) } IsHeap(h) && h[o, closed] && o != o' && Set#Equal(Set#Singleton(o''), h[o, owns]) ==> 
	(in_domain(h, o, o') <==> in_domain(h, o'', o')));
	

// Frame axiom: domain frames itself
axiom (forall h, h': HeapType, x, x': ref :: { in_domain(h, x, x'), in_domain(h', x, x'), HeapSucc(h, h') } 
  IsHeap(h) && IsHeap(h') && HeapSucc(h, h') &&
  h[x, allocated] && h'[x, allocated] &&     
  (forall <T> o: ref, f: Field T :: h[o, allocated] ==> h'[o, f] == h[o, f] || !in_domain(h, x, o))
  ==> in_domain(h', x, x') == in_domain(h, x, x'));

function domain(h: HeapType, o: ref): Set ref
{ (lambda o': ref :: in_domain(h, o, o')) }

// Is o' in the transitive owns of o?
// (the same as in_domain if o is closed)
function in_trans_owns(h: HeapType, o: ref, o': ref): bool
{
  o == o' || h[o, owns][o'] || (exists x: ref :: h[o, owns][x] && in_trans_owns(h, x, o'))
}

function trans_owns(h: HeapType, o: ref): Set ref
{ (lambda o': ref :: in_trans_owns(h, o, o')) }

const universe: Set ref;
axiom (forall o: ref :: { universe[o] } universe[o]);

// ----------------------------------------------------------------------
// Models

function IsModelField<alpha>(field: Field alpha, t: Type): bool; // Is this field a model field in class t?

axiom (forall <alpha> f: Field alpha :: { IsModelField(f, ANY) }
  IsModelField(f, ANY) <==> f == closed || f == owner || f == owns || f == observers || f == subjects );  

// ----------------------------------------------------------------------
// Frames

// Set of object-field pairs
type Frame = <alpha>[ref, Field alpha]bool;

function Frame#Subset(Frame, Frame): bool;
axiom(forall a: Frame, b: Frame :: { Frame#Subset(a,b) }
  Frame#Subset(a,b) <==> (forall <alpha> o: ref, f: Field alpha :: {a[o, f]} {b[o, f]} a[o, f] ==> b[o, f]));
	
function Frame#Singleton(ref): Frame;
axiom(forall <alpha> o, o': ref, f: Field alpha :: { Frame#Singleton(o)[o', f] }
  Frame#Singleton(o)[o', f] <==> o == o');

function has_whole_object(frame: Frame, o: ref): bool
{ (forall <alpha> f: Field alpha :: frame[o, f]) }

// Frame is closed under ownership domains and includes all unallocated objects
function { :inline } closed_under_domains(frame: Frame, h: HeapType): bool
{ 
  (forall <U> o': ref, f': Field U :: {frame[o', f']} 
    !h[o', allocated] || (exists <V> o: ref, f: Field V :: frame[o, f] && in_domain(h, o, o') && o != o') ==> frame[o', f'])
}

// Objects outside of ownership domains of frame did not change, unless they were newly allocated
function {: inline } same_outside(h: HeapType, h': HeapType, frame: Frame): bool { 
	(forall <T> o: ref, f: Field T :: { h'[o, f] }
    o != Void && h[o, allocated] ==>      
      h'[o, f] == h[o, f] ||
      frame[o, f] ||        
      (exists o': ref :: {frame[o', closed]} o' != o && frame[o', closed] && in_domain(h, o', o)) // Using extra knowledge here to remove an existential: modifying object's domain requires its closed to be in the frame
  )
}

// Objects outside of frame did not change, unless they were newly allocated
function {: inline } flat_same_outside(h: HeapType, h': HeapType, frame: Frame): bool { 
	(forall <T> o: ref, f: Field T :: { h'[o, f] } o != Void && h[o, allocated] ==> h'[o, f] == h[o, f] || frame[o, f])
}

// Objects inside the frame did not change
function same_inside(h: HeapType, h': HeapType, frame: Frame): bool { 
	(forall <T> o: ref, f: Field T :: o != Void && h[o, allocated] && h'[o, allocated] && frame [o, f] ==> h'[o, f] == h[o, f])
}
// This version corresponds to the old semantics of read clauses:
// // Objects inside the old ownership domains of frame did not change
// // function same_inside(h: HeapType, h': HeapType, frame: Frame): bool { 
	// // (forall <T> o: ref, f: Field T :: { h[o, f] } { h'[o, f] }
    // // h[o, allocated] && h'[o, f] != h[o, f] ==>
      // // !frame [o, f] && (forall<U> o': ref, g: Field U :: frame[o', g] && o != o' ==> !in_domain(h, o', o)))
// // }

// Set of all writable objects
const writable: Frame;

// Set of all readable objects
const readable: Frame;

// ----------------------------------------------------------------------
// Invariants

// Is invariant of object o satisifed?
function user_inv(h: HeapType, o: ref): bool;

// Read frame of user_inv
function user_inv_readable(HeapType, ref): Frame;
axiom (forall<T> h: HeapType, x: ref, o: ref, f: Field T :: { user_inv_readable(h, x)[o, f] }
  IsHeap(h) ==> user_inv_readable(h, x)[o, f] == (in_trans_owns(h, x, o) || h[x, subjects][o]));
  
// Uninterpreted function to trigger the invariant frame axiom
function inv_frame_trigger(x: ref): bool;
  
// Frame axiom
axiom (forall h, h': HeapType, x: ref :: { user_inv(h, x), user_inv(h', x), HeapSucc(h, h'), inv_frame_trigger(x) } 
  IsHeap(h) && IsHeap(h') && HeapSucc(h, h') && inv_frame_trigger(x) &&
  x != Void && h[x, allocated] && h'[x, allocated] &&
  is_open(h, x) && is_open(h', x) &&
  user_inv(h, x) && 
  (forall <T> o: ref, f: Field T :: h[o, allocated] ==> // every object's field
      h'[o, f] == h[o, f] ||                            // is unchanged
      f == closed || f == owner ||                      // or is outside of the read set of the invariant
      !user_inv_readable(h, x)[o, f]
      // (!in_trans_owns(h, x, o) && guard(h, o, f, h'[o, f], x)) // or changed in a way that conforms to its guard
   )
  ==> user_inv(h', x));

// Is object o closed or the invariant satisfied?
function {:inline true} inv(h: HeapType, o: ref): bool {
	h[o, closed] ==> user_inv(h, o)
}

// Global heap invariants
function {:inline true} global(h: HeapType): bool
{
  h[Void, allocated] && is_open(h, Void) &&
  // (forall o: ref :: h[o, allocated] && is_open(h, o) ==> is_free(h, o)) &&
  // (forall o: ref :: { h[o, owner], is_open(h, o) } h[o, allocated] && is_open(h, o) ==> is_free(h, o)) &&
  (forall o: ref, o': ref :: { h[o, owns][o'] } h[o, allocated] && h[o', allocated] && h[o, closed] && h[o, owns][o'] ==> (h[o', closed] && h[o', owner] == o)) && // G2
  (forall o: ref :: { user_inv(h, o) } h[o, allocated] ==> inv(h, o)) // G1
}

// All objects in valid heaps are valid.
// This function introduces invariants automatically, so should be used with care.
function {: inline } global_permissive(): bool
{ (forall h: HeapType, o: ref :: {is_wrapped (h, o)}{is_closed (h, o)} IsHeap(h) && h[o, allocated] ==> inv(h, o)) }

// Condition under which an update heap[current, f] := v is guaranteed to preserve the invariant of o.
function guard<T>(heap: HeapType, current: ref, f: Field T, v: T, o: ref): bool;

// All subjects know current for an observer
function {: inline } admissibility2 (heap: HeapType, current: ref): bool
{ 
  (forall s: ref :: heap[current, subjects][s] && s != Void ==> heap[s, observers][current]) 
}

// Invariant cannot be invalidated by an update that conform to its guard
function {: inline } admissibility3 (heap: HeapType, current: ref): bool
{
  (forall<T> s: ref, f: Field T, v: T ::
    heap[current, subjects][s] && s != current && s != Void && IsHeap(heap[s, f := v]) && guard(heap, s, f, v, current) ==>
      user_inv(heap[s, f := v], current))
}

// ----------------------------------------------------------------------
// Built-in operations

// Allocate fresh object
procedure allocate(t: Type) returns (result: ref);
  modifies Heap;
  ensures global(Heap);
  ensures !old(Heap[result, allocated]); // AL1
  ensures Heap[result, allocated]; // AL2
  ensures result != Void;
  ensures type_of(result) == t;
  ensures (forall<T> f: Field T :: f != allocated ==> Heap[result, f] == Default(f));
  ensures has_whole_object(writable, result);
  ensures (forall <T> o: ref, f: Field T :: o != result ==> Heap[o, f] == old(Heap[o, f]));
  free ensures HeapSucc(old(Heap), Heap);

// Update Heap position Current.field with value.
procedure update_heap<T>(Current: ref, field: Field T, value: T);
  requires (Current != Void) && (Heap[Current, allocated]); // type:assign tag:attached_and_allocated
  requires field != closed && field != owner; // type:assign tag:closed_or_owner_not_allowed UP4
  requires is_open(Heap, Current); // type:assign tag:target_open UP1
  requires (forall o: ref :: Heap[Current, observers][o] ==> (is_open(Heap, o) || (IsHeap(Heap[Current, field := value]) ==> guard(Heap, Current, field, value, o)))); // type:assign tag:observers_open_or_guard_holds UP2  
  requires writable[Current, field]; // type:assign tag:attribute_writable UP3
  modifies Heap;
  ensures global(Heap);
  ensures Heap == old(Heap[Current, field := value]);
  free ensures HeapSucc(old(Heap), Heap);
  
// Unwrap o
procedure unwrap(o: ref);
  requires (o != Void) && (Heap[o, allocated]); // type:pre tag:attached
  requires is_wrapped(Heap, o); // type:pre tag:wrapped UW1
  requires writable[o, closed]; // type:pre tag:writable UW2
  modifies Heap;
  ensures global(Heap);  
  ensures is_open(Heap, o); // UWE1
  ensures (forall o': ref :: old(Heap[o, owns][o']) ==> is_wrapped(Heap, o')); // UWE2
  ensures (forall <T> o': ref, f: Field T :: !(o' == o && f == closed) && !(old(Heap[o, owns][o']) && f == owner) ==> Heap[o', f] == old(Heap[o', f]));
  free ensures HeapSucc(old(Heap), Heap);

procedure unwrap_all (Current: ref, s: Set ref);
  requires (forall o: ref :: s[o] ==> (o != Void) && (Heap[o, allocated])); // type:pre tag:attached
  requires (forall o: ref :: s[o] ==> is_wrapped(Heap, o)); // type:pre tag:wrapped UW1
  requires (forall o: ref :: s[o] ==> writable[o, closed]); // type:pre tag:writable UW2
  modifies Heap;
  ensures global(Heap);
  ensures (forall o: ref :: s[o] ==> is_open(Heap, o)); // UWE1
  ensures (forall o: ref :: s[o] ==> (forall o': ref :: old(Heap[o, owns][o']) ==> is_wrapped(Heap, o'))); // UWE2
  ensures (forall <T> o: ref, f: Field T :: !(f == closed && s[o]) && !(f == owner && (exists o': ref :: s[o'] && old(Heap[o', owns][o]))) ==> Heap[o, f] == old(Heap[o, f]));
  ensures (forall o: ref :: s[o] ==> user_inv(Heap, o) && inv_frame_trigger(o));
  free ensures HeapSucc(old(Heap), Heap);

// Wrap o
procedure wrap(o: ref);
  requires (o != Void) && (Heap[o, allocated]); // type:pre tag:attached
  requires is_open(Heap, o); // type:pre tag:open W1
  requires writable[o, closed]; // type:pre tag:writable W4
  // requires user_inv(Heap, o); // type:pre tag:invariant_holds W2 // Custom check now
  requires (forall o': ref :: { Heap[o, owns][o'] } Heap[o, owns][o'] ==> is_wrapped(Heap, o') && writable[o', owner]); // type:pre tag:owned_objects_wrapped_and_writable W3
  modifies Heap;
  ensures global(Heap);  
  ensures (forall o': ref :: old(Heap[o, owns][o']) ==> Heap[o', owner] == o); // WE2
  ensures is_wrapped(Heap, o); // WE3
  ensures (forall <T> o': ref, f: Field T :: !(o' == o && f == closed) && !(old(Heap[o, owns][o']) && f == owner) ==> Heap[o', f] == old(Heap[o', f]));
  free ensures HeapSucc(old(Heap), Heap);

procedure wrap_all(Current: ref, s: Set ref);
  requires (forall o: ref :: s[o] ==> (o != Void) && (Heap[o, allocated])); // type:pre tag:attached
  requires (forall o: ref :: s[o] ==> is_open(Heap, o)); // type:pre tag:open W1
  requires (forall o: ref :: s[o] ==> writable[o, closed]); // type:pre tag:writable W4    
  requires (forall o: ref :: s[o] ==> user_inv(Heap, o)); // type:pre tag:invariant_holds W2
  requires (forall o: ref :: s[o] ==> (forall o': ref :: Heap[o, owns][o'] ==> is_wrapped(Heap, o') && writable[o', owner])); // type:pre tag:owned_objects_wrapped_and_writable W3
  modifies Heap;
  ensures global(Heap);  
  ensures (forall o: ref :: s[o] ==> (forall o': ref :: old(Heap[o, owns][o']) ==> Heap[o', owner] == o)); // WE2
  ensures (forall o: ref :: s[o] ==> is_wrapped(Heap, o)); // WE3
  ensures (forall <T> o: ref, f: Field T :: !(f == closed && s[o]) && !(f == owner && (exists o': ref :: s[o'] && old(Heap[o', owns][o]))) ==> Heap[o, f] == old(Heap[o, f]));
  free ensures HeapSucc(old(Heap), Heap);

// ----------------------------------------------------------------------
// Attached/Detachable functions

// Reference `o' is attached to an object of type `t' on heap `heap'.
function attached_exact(heap: HeapType, o: ref, t: Type) returns (bool) {
	(o != Void) && (heap[o, allocated]) && (type_of(o) == t)
}

// Reference `o' is either Void or attached to an object of type `t' on heap `heap'.
function detachable_exact(heap: HeapType, o: ref, t: Type) returns (bool) {
	(o == Void) || attached_exact(heap, o, t)
}

// Reference `o' is attached and conforms to type `t' on heap `heap'.
function attached(heap: HeapType, o: ref, t: Type) returns (bool) {
	(o != Void) && (heap[o, allocated]) && (type_of(o) <: t)
}

// Reference `o' is either Void or attached and conforms to `t' on heap `heap'.
function detachable(heap: HeapType, o: ref, t: Type) returns (bool) {
	(o == Void) || attached(heap, o, t)
}

// ----------------------------------------------------------------------
// Basic types

// Integer boxing

const unique INTEGER: Type;

function boxed_int(i: int) returns (ref);
function unboxed_int(r: ref) returns (int);

axiom (forall i: int :: unboxed_int(boxed_int(i)) == i);
axiom (forall i1, i2: int :: (i1 == i2) ==> (boxed_int(i1) == boxed_int(i2)));
axiom (forall i: int :: boxed_int(i) != Void && type_of(boxed_int(i)) == INTEGER);
axiom (forall heap: HeapType, i: int :: IsHeap(heap) ==> heap[boxed_int(i), allocated]);


// Boolean boxing

const unique BOOLEAN: Type;
const unique boxed_true: ref;
const unique boxed_false: ref;

function boxed_bool(b: bool) returns (ref);
function unboxed_bool(r: ref) returns (bool);

axiom (boxed_bool(true) == boxed_true);
axiom (boxed_bool(false) == boxed_false);
axiom (unboxed_bool(boxed_true) == true);
axiom (unboxed_bool(boxed_false) == false);
axiom (boxed_true != boxed_false);
axiom (boxed_true != Void && type_of(boxed_true) == BOOLEAN);
axiom (boxed_false != Void && type_of(boxed_false) == BOOLEAN);
axiom (forall heap: HeapType :: IsHeap(heap) ==> heap[boxed_true, allocated]);
axiom (forall heap: HeapType :: IsHeap(heap) ==> heap[boxed_false, allocated]);

// Bounded integers

function is_integer_8(i: int) returns (bool) {
	(-128 <= i) && (i <= 127)
}
function is_integer_16(i: int) returns (bool) {
	(-32768 <= i) && (i <= 32767)
}
function is_integer_32(i: int) returns (bool) {
	(-2147483648 <= i) && (i <= 2147483647)
}
function is_integer_64(i: int) returns (bool) {
	(-9223372036854775808 <= i) && (i <= 9223372036854775807)
}
function is_natural(i: int) returns (bool) {
	(0 <= i)
}
function is_natural_8(i: int) returns (bool) {
	(0 <= i) && (i <= 255)
}
function is_natural_16(i: int) returns (bool) {
	(0 <= i) && (i <= 65535)
}
function is_natural_32(i: int) returns (bool) {
	(0 <= i) && (i <= 4294967295)
}
function is_natural_64(i: int) returns (bool) {
	(0 <= i) && (i <= 18446744073709551615)
}

// Numeric conversions

function int_to_integer_8(i: int) returns (int);
axiom (forall i: int :: { int_to_integer_8(i) } is_integer_8(i) ==> int_to_integer_8(i) == i);
axiom (forall i: int :: { int_to_integer_8(i) } is_integer_8(int_to_integer_8(i)));

function int_to_integer_16(i: int) returns (int);
axiom (forall i: int :: { int_to_integer_16(i) } is_integer_16(i) ==> int_to_integer_16(i) == i);
axiom (forall i: int :: { int_to_integer_16(i) } is_integer_16(int_to_integer_16(i)));

function int_to_integer_32(i: int) returns (int);
axiom (forall i: int :: { int_to_integer_32(i) } is_integer_32(i) ==> int_to_integer_32(i) == i);
axiom (forall i: int :: { int_to_integer_32(i) } is_integer_32(int_to_integer_32(i)));

function int_to_integer_64(i: int) returns (int);
axiom (forall i: int :: { int_to_integer_64(i) } is_integer_64(i) ==> int_to_integer_64(i) == i);
axiom (forall i: int :: { int_to_integer_64(i) } is_integer_64(int_to_integer_64(i)));

function int_to_natural_8(i: int) returns (int);
axiom (forall i: int :: { int_to_natural_8(i) } is_natural_8(i) ==> int_to_natural_8(i) == i);
axiom (forall i: int :: { int_to_natural_8(i) } is_natural_8(int_to_natural_8(i)));

function int_to_natural_16(i: int) returns (int);
axiom (forall i: int :: { int_to_natural_16(i) } is_natural_16(i) ==> int_to_natural_16(i) == i);
axiom (forall i: int :: { int_to_natural_16(i) } is_natural_16(int_to_natural_16(i)));

function int_to_natural_32(i: int) returns (int);
axiom (forall i: int :: { int_to_natural_32(i) } is_natural_32(i) ==> int_to_natural_32(i) == i);
axiom (forall i: int :: { int_to_natural_32(i) } is_natural_32(int_to_natural_32(i)));

function int_to_natural_64(i: int) returns (int);
axiom (forall i: int :: { int_to_natural_64(i) } is_natural_64(i) ==> int_to_natural_64(i) == i);
axiom (forall i: int :: { int_to_natural_64(i) } is_natural_64(int_to_natural_64(i)));

function real_to_integer_32(r: real) returns (int);
axiom (forall r: real :: { real_to_integer_32(r) } is_integer_32(int(r)) ==> real_to_integer_32(r) == int(r));
axiom (forall r: real :: { real_to_integer_32(r) } (!is_integer_32(int(r)) && r < 0.0) ==> real_to_integer_32(r) == -2147483648);
axiom (forall r: real :: { real_to_integer_32(r) } (!is_integer_32(int(r)) && r > 0.0) ==> real_to_integer_32(r) ==  2147483647);

function real_to_integer_64(r: real) returns (int);
axiom (forall r: real :: { real_to_integer_64(r) } is_integer_64(int(r)) ==> real_to_integer_64(r) == int(r));
axiom (forall r: real :: { real_to_integer_64(r) } (!is_integer_64(int(r)) && r < 0.0) ==> real_to_integer_64(r) == -9223372036854775808);
axiom (forall r: real :: { real_to_integer_64(r) } (!is_integer_64(int(r)) && r > 0.0) ==> real_to_integer_64(r) ==  9223372036854775807);

// Arithmetic functions

function add(a, b: int): int { a + b }
function subtract(a, b: int): int { a - b }
function multiply(a, b: int): int { a * b }
function modulo(a, b: int): int { a mod b }
function divide(a, b: int): int { a div b }

function min(a, b: int): int { if a <= b then a else b }
function max(a, b: int): int { if a >= b then a else b }
function abs(a: int): int { if a >= 0 then a else -a }
function sign(a: int): int { if a == 0 then 0 else if a > 0 then 1 else -1 }

function min_real(a, b: real): real { if a <= b then a else b }
function max_real(a, b: real): real { if a >= b then a else b }
function abs_real(a: real): real { if a >= 0.0 then a else -a }
function sign_real(a: real): int { if a == 0.0 then 0 else if a > 0.0 then 1 else -1 }

function bit_and(a, b: int): int;
function bit_or(a, b: int): int;
function bit_xor(a, b: int): int;
function bit_not(a: int): int;
function bit_shift_left(a, n: int): int;
function bit_shift_right(a, n: int): int;

// ----------------------------------------------------------------------
// once procedures

function global_once_value<T>(rid: int): T;
function object_once_value<T>(o: ref, rid: int): T;


// Expanded types

// type unknown;

// Address operator

// function address(a: ref) returns (int);
// axiom (forall a, b: ref :: (a != b) <==> (address(a) != address(b))); // Different objects have different heap addresses.
// axiom (forall a: ref :: is_integer_64(address(a))); // Addresses are 64 bit integers.

// Unsupported

function unsupported<T>() returns (T);


// Custom content

const unique V_ARRAY2^ANY^: Type;

axiom ((V_ARRAY2^ANY^) <: (V_MUTABLE_SEQUENCE^ANY^));

axiom ((forall t: Type :: { (V_ARRAY2^ANY^) <: (t) } ((V_ARRAY2^ANY^) <: (t)) <==> (((t) == (V_ARRAY2^ANY^)) || ((V_MUTABLE_SEQUENCE^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_ARRAY2^ANY^)) == (-1));

axiom ((FieldId(closed, V_ARRAY2^ANY^)) == (-2));

axiom ((FieldId(owner, V_ARRAY2^ANY^)) == (-3));

axiom ((FieldId(owns, V_ARRAY2^ANY^)) == (-4));

axiom ((FieldId(observers, V_ARRAY2^ANY^)) == (-5));

axiom ((FieldId(subjects, V_ARRAY2^ANY^)) == (-6));

axiom ((forall <T0> $f: Field T0 :: { IsModelField($f, V_ARRAY2^ANY^) } (IsModelField($f, V_ARRAY2^ANY^)) <==> ((($f) == (V_ARRAY2^ANY^.sequence)) || (($f) == (V_ARRAY2^ANY^.column_count)) || (($f) == (V_ARRAY2^ANY^.lower_)) || (($f) == (V_ARRAY2^ANY^.bag)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_ARRAY2^ANY^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (!(heap[current, observers][current])) && ((Seq#IsEmpty(heap[current, V_ARRAY2^ANY^.sequence])) ==> ((heap[current, V_ARRAY2^ANY^.lower_]) == (1))) && (Bag#Equal(heap[current, V_ARRAY2^ANY^.bag], Seq#ToBag(heap[current, V_ARRAY2^ANY^.sequence]))) && ((heap[current, V_ARRAY2^ANY^.array]) != (Void)) && (Set#Equal(heap[current, owns], Set#Singleton(heap[current, V_ARRAY2^ANY^.array]))) && ((heap[heap[current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.lower_]) == (1)) && (Set#IsEmpty(heap[heap[current, V_ARRAY2^ANY^.array], observers])) && (Seq#Equal(heap[current, V_ARRAY2^ANY^.sequence], heap[heap[current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence])) && ((heap[current, V_ARRAY2^ANY^.lower_]) == (1)) && ((Seq#IsEmpty(heap[current, V_ARRAY2^ANY^.sequence])) ==> ((heap[current, V_ARRAY2^ANY^.column_count]) == (0))) && ((!(Seq#IsEmpty(heap[current, V_ARRAY2^ANY^.sequence]))) ==> ((heap[current, V_ARRAY2^ANY^.column_count]) > (0))) && (((heap[current, V_ARRAY2^ANY^.row_count]) * (heap[current, V_ARRAY2^ANY^.column_count])) == (Seq#Length(heap[current, V_ARRAY2^ANY^.sequence]))) && (Set#IsEmpty(heap[current, subjects])) && (admissibility2(heap, current))
}

function V_ARRAY2^ANY^.V_ARRAY2^ANY^.bag.static(heap: HeapType, current: ref) returns (Bag (ref)) {
  Seq#ToBag(heap[current, V_ARRAY2^ANY^.sequence])
}

function V_ARRAY2^ANY^.owns.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, V_ARRAY2^ANY^.array])
}

function V_ARRAY2^ANY^.V_ARRAY2^ANY^.sequence.static(heap: HeapType, current: ref) returns (Seq (ref)) {
  heap[heap[current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence]
}

function V_ARRAY2^ANY^.V_ARRAY2^ANY^.lower_.static(heap: HeapType, current: ref) returns (int) {
  1
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((user_inv(heap, current)) <==> (V_ARRAY2^ANY^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_ARRAY2^ANY^)) ==> ((user_inv(heap, current)) ==> (V_ARRAY2^ANY^.user_inv(heap, current)))));

procedure V_ARRAY2.invariant_admissibility_check(Current: ref);
  requires attached_exact(Heap, Current, V_ARRAY2^ANY^);



implementation V_ARRAY2.invariant_admissibility_check(Current: ref)
{
  entry:
  goto pre, a2, a3;
  pre:
  assume !(Heap[Current, observers][Current]);
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.sequence]; // type:access tag:attribute_readable line:236 cid:338 fid:88
  assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> (user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.lower_]); // type:access tag:attribute_readable line:236 cid:338 fid:93
  assume (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.lower_]) == (1));
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.bag]; // type:access tag:attribute_readable line:237 cid:338 fid:78
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.sequence]; // type:access tag:attribute_readable line:237 cid:338 fid:88
  assume Bag#Equal(Heap[Current, V_ARRAY2^ANY^.bag], Seq#ToBag(Heap[Current, V_ARRAY2^ANY^.sequence]));
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:253 cid:338 fid:117
  assume (Heap[Current, V_ARRAY2^ANY^.array]) != (Void);
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:254 cid:338 fid:117
  assume Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, V_ARRAY2^ANY^.array]));
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:255 cid:338 fid:117
  assert {:subsumption 0} (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:attached tag:array_lower_definition line:255
  assert user_inv_readable(Heap, Current)[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.lower_]; // type:access tag:attribute_readable line:255 cid:63 fid:93
  assume (Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.lower_]) == (1);
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:256 cid:338 fid:117
  assert {:subsumption 0} (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:attached tag:array_no_observers line:256
  assume Set#IsEmpty(Heap[Heap[Current, V_ARRAY2^ANY^.array], observers]);
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.sequence]; // type:access tag:attribute_readable line:257 cid:338 fid:88
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:257 cid:338 fid:117
  assert {:subsumption 0} (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:attached tag:sequence_implementation line:257
  assert user_inv_readable(Heap, Current)[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence]; // type:access tag:attribute_readable line:257 cid:63 fid:88
  assume Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence]);
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.lower_]; // type:access tag:attribute_readable line:258 cid:338 fid:93
  assume (Heap[Current, V_ARRAY2^ANY^.lower_]) == (1);
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.sequence]; // type:access tag:attribute_readable line:259 cid:338 fid:88
  assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> (user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.column_count]); // type:access tag:attribute_readable line:259 cid:338 fid:104
  assume (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) == (0));
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.sequence]; // type:access tag:attribute_readable line:260 cid:338 fid:88
  assert (!(Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence]))) ==> (user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.column_count]); // type:access tag:attribute_readable line:260 cid:338 fid:104
  assume (!(Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence]))) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) > (0));
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.row_count]; // type:access tag:attribute_readable line:261 cid:338 fid:103
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:261 cid:338 fid:104
  assert user_inv_readable(Heap, Current)[Current, V_ARRAY2^ANY^.sequence]; // type:access tag:attribute_readable line:261 cid:338 fid:88
  assume ((Heap[Current, V_ARRAY2^ANY^.row_count]) * (Heap[Current, V_ARRAY2^ANY^.column_count])) == (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence]));
  return;
  a2:
  assume user_inv(Heap, Current);
  assert admissibility2(Heap, Current); // type:A2
  return;
  a3:
  assume user_inv(Heap, Current);
  assert admissibility3(Heap, Current); // type:A3
  return;
}

procedure V_ARRAY2^ANY^.forget_iterator(Current: ref, it: ref);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires detachable(Heap, it, V_ITERATOR^ANY^); // info:type property for argument it
  modifies Heap;
  requires is_wrapped(Heap, Current); // type:pre tag:wrapped line:129
  requires (it) != (Void); // type:attached tag:it_wrapped line:130
  requires is_wrapped(Heap, it); // type:pre tag:it_wrapped line:130
  requires (Heap[it, V_ITERATOR^ANY^.target]) == (Current); // type:pre tag:valid_target line:131
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:136
  ensures (it) != (Void); // type:attached tag:it_open line:137
  ensures is_open(Heap, it); // type:post tag:it_open line:137
  ensures Set#Equal(Heap[Current, observers], Set#Removed(old(Heap)[Current, observers], it)); // type:post tag:observer_removed line:138
  ensures Set#Equal(Heap[it, owns], old(Heap)[it, owns]); // type:post tag:it.owns ~ old it.owns line:139
  ensures Set#Equal(Heap[it, observers], old(Heap)[it, observers]); // type:post tag:it.observers ~ old it.observers line:140
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.forget_iterator(Heap, Current, it), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.forget_iterator(old(Heap), Current, it));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.V_ARRAY2^ANY^.forget_iterator.1(heap: HeapType, current: ref, it: ref) returns (ref) {
  it
}

implementation V_ARRAY2^ANY^.forget_iterator(Current: ref, it: ref)
{
  entry:
  assume {:captureState "V_ARRAY2^ANY^.forget_iterator"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:55 line:123
  assume V_ARRAY2^ANY^.user_inv(Heap, Current);
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/container/v_container.e:133
  // it.unwrap
  assert {:subsumption 0} (it) != (Void); // type:attached line:133
  call unwrap(it); // line:133 cid:1 rid:55
  assume user_inv(Heap, it);
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/container/v_container.e:134
  // set_observers (observers / it)
  call update_heap(Current, observers, Set#Removed(Heap[Current, observers], it)); // line:134
  if (modify.V_ARRAY2^ANY^.forget_iterator(Heap, Current, it)[Current, V_ARRAY2^ANY^.sequence]) {
    call update_heap(Current, V_ARRAY2^ANY^.sequence, V_ARRAY2^ANY^.V_ARRAY2^ANY^.sequence.static(Heap, Current)); // default:sequence line:143
  }
  if (modify.V_ARRAY2^ANY^.forget_iterator(Heap, Current, it)[Current, V_ARRAY2^ANY^.lower_]) {
    call update_heap(Current, V_ARRAY2^ANY^.lower_, V_ARRAY2^ANY^.V_ARRAY2^ANY^.lower_.static(Heap, Current)); // default:lower_ line:143
  }
  if (modify.V_ARRAY2^ANY^.forget_iterator(Heap, Current, it)[Current, V_ARRAY2^ANY^.bag]) {
    call update_heap(Current, V_ARRAY2^ANY^.bag, V_ARRAY2^ANY^.V_ARRAY2^ANY^.bag.static(Heap, Current)); // default:bag line:143
  }
  if (modify.V_ARRAY2^ANY^.forget_iterator(Heap, Current, it)[Current, owns]) {
    call update_heap(Current, owns, V_ARRAY2^ANY^.owns.static(Heap, Current)); // default:owns line:143
  }
  if (*) {
    assert !(Heap[Current, observers][Current]); // type:inv tag:not_observer line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.lower_]) == (1)); // type:inv tag:lower_constraint line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Bag#Equal(Heap[Current, V_ARRAY2^ANY^.bag], Seq#ToBag(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:bag_definition line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:inv tag:array_exists line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, V_ARRAY2^ANY^.array])); // type:inv tag:owns_definition line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.lower_]) == (1); // type:inv tag:array_lower_definition line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Heap[Current, V_ARRAY2^ANY^.array], observers]); // type:inv tag:array_no_observers line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence]); // type:inv tag:sequence_implementation line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.lower_]) == (1); // type:inv tag:lower_definition line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) == (0)); // type:inv tag:column_count_empty line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (!(Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence]))) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) > (0)); // type:inv tag:column_count_nonempty line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert ((Heap[Current, V_ARRAY2^ANY^.row_count]) * (Heap[Current, V_ARRAY2^ANY^.column_count])) == (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:row_count_definition line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:143 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:143 cid:1 rid:53
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:53 line:143
}

procedure V_ARRAY2^ANY^.add_iterator(Current: ref, it: ref);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires detachable(Heap, it, V_ITERATOR^ANY^); // info:type property for argument it
  modifies Heap;
  requires is_wrapped(Heap, Current); // type:pre tag:wrapped line:152
  requires attached(Heap, it, V_ARRAY_ITERATOR^ANY^); // type:pre tag:valid_type line:153
  ensures is_wrapped(Heap, Current); // type:post tag:wrapped line:159
  ensures Set#Equal(Heap[Current, observers], Set#Extended(old(Heap)[Current, observers], it)); // type:post tag:observer_added line:160
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.add_iterator(Heap, Current, it), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.add_iterator(old(Heap), Current, it));
  free ensures HeapSucc(old(Heap), Heap);



function { :inline } variant.V_ARRAY2^ANY^.add_iterator.1(heap: HeapType, current: ref, it: ref) returns (ref) {
  it
}

implementation V_ARRAY2^ANY^.add_iterator(Current: ref, it: ref)
{
  entry:
  assume {:captureState "V_ARRAY2^ANY^.add_iterator"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/container/v_container.e:155
  // unwrap
  call unwrap(Current); // line:155 cid:1 rid:55
  assume V_ARRAY2^ANY^.user_inv(Heap, Current);
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/container/v_container.e:156
  // set_observers (observers & it)
  call update_heap(Current, observers, Set#Extended(Heap[Current, observers], it)); // line:156
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/container/v_container.e:157
  // wrap
  if (modify.V_ARRAY2^ANY^.add_iterator(Heap, Current, it)[Current, V_ARRAY2^ANY^.sequence]) {
    call update_heap(Current, V_ARRAY2^ANY^.sequence, V_ARRAY2^ANY^.V_ARRAY2^ANY^.sequence.static(Heap, Current)); // default:sequence line:157
  }
  if (modify.V_ARRAY2^ANY^.add_iterator(Heap, Current, it)[Current, V_ARRAY2^ANY^.lower_]) {
    call update_heap(Current, V_ARRAY2^ANY^.lower_, V_ARRAY2^ANY^.V_ARRAY2^ANY^.lower_.static(Heap, Current)); // default:lower_ line:157
  }
  if (modify.V_ARRAY2^ANY^.add_iterator(Heap, Current, it)[Current, V_ARRAY2^ANY^.bag]) {
    call update_heap(Current, V_ARRAY2^ANY^.bag, V_ARRAY2^ANY^.V_ARRAY2^ANY^.bag.static(Heap, Current)); // default:bag line:157
  }
  if (modify.V_ARRAY2^ANY^.add_iterator(Heap, Current, it)[Current, owns]) {
    call update_heap(Current, owns, V_ARRAY2^ANY^.owns.static(Heap, Current)); // default:owns line:157
  }
  if (*) {
    assert !(Heap[Current, observers][Current]); // type:inv tag:not_observer line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.lower_]) == (1)); // type:inv tag:lower_constraint line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Bag#Equal(Heap[Current, V_ARRAY2^ANY^.bag], Seq#ToBag(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:bag_definition line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:inv tag:array_exists line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, V_ARRAY2^ANY^.array])); // type:inv tag:owns_definition line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.lower_]) == (1); // type:inv tag:array_lower_definition line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Heap[Current, V_ARRAY2^ANY^.array], observers]); // type:inv tag:array_no_observers line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence]); // type:inv tag:sequence_implementation line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.lower_]) == (1); // type:inv tag:lower_definition line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) == (0)); // type:inv tag:column_count_empty line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (!(Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence]))) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) > (0)); // type:inv tag:column_count_nonempty line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert ((Heap[Current, V_ARRAY2^ANY^.row_count]) * (Heap[Current, V_ARRAY2^ANY^.column_count])) == (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:row_count_definition line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:157 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:157 cid:1 rid:53
    assume false;
  }
  call wrap(Current); // line:157 cid:1 rid:53
}

procedure create.V_ARRAY2^ANY^.make(Current: ref, n: int, m: int);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(n); // info:type property for argument n
  free requires is_integer_32(m); // info:type property for argument m
  modifies Heap;
  requires (((n) == (0)) && ((m) == (0))) || (((n) > (0)) && ((m) > (0))); // type:pre tag:valid_dimensions line:38
  ensures (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])) == ((n) * (m)); // type:post tag:sequence_domain_definition line:45
  ensures Seq#IsConstant(Heap[Current, V_ARRAY2^ANY^.sequence], Void); // type:post tag:sequence_definition line:46
  ensures (Heap[Current, V_ARRAY2^ANY^.column_count]) == (m); // type:post tag:column_count_definition line:47
  ensures Set#IsEmpty(Heap[Current, observers]); // type:post tag:no_observers line:48
  requires (forall <T3> $f: Field T3 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.make(Heap, Current, n, m), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.make(old(Heap), Current, n, m));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.V_ARRAY2^ANY^.make(Current: ref, n: int, m: int)
{
  var temp_1: ref;
  var temp_2: Seq (ref);

  init_locals:
  temp_1 := Void;
  temp_2 := Seq#Empty();

  entry:
  assume {:captureState "create.V_ARRAY2^ANY^.make"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:40
  // row_count := n
  call update_heap(Current, V_ARRAY2^ANY^.row_count, n); // line:40
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:41
  // column_count := m
  call update_heap(Current, V_ARRAY2^ANY^.column_count, m); // line:41
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:42
  // create array.make (1, n * m)
  call temp_1 := allocate(V_ARRAY^ANY^); // line:-1
  call create.V_ARRAY^ANY^.make(temp_1, 1, (n) * (m)); // line:42 cid:63 rid:3182
  call update_heap(Current, V_ARRAY2^ANY^.array, temp_1); // line:42
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:43
  // create sequence.constant (({G}).default, n * m)
  assert pre.fun.MML_SEQUENCE^ANY^.constant(Void, (n) * (m)); // type:check tag:function_precondition line:43 cid:130 rid:3027
  call update_heap(Current, V_ARRAY2^ANY^.sequence, Seq#Constant(Void, (n) * (m))); // line:43
  if (modify.V_ARRAY2^ANY^.make(Heap, Current, n, m)[Current, V_ARRAY2^ANY^.sequence]) {
    call update_heap(Current, V_ARRAY2^ANY^.sequence, V_ARRAY2^ANY^.V_ARRAY2^ANY^.sequence.static(Heap, Current)); // default:sequence line:49
  }
  if (modify.V_ARRAY2^ANY^.make(Heap, Current, n, m)[Current, V_ARRAY2^ANY^.lower_]) {
    call update_heap(Current, V_ARRAY2^ANY^.lower_, V_ARRAY2^ANY^.V_ARRAY2^ANY^.lower_.static(Heap, Current)); // default:lower_ line:49
  }
  if (modify.V_ARRAY2^ANY^.make(Heap, Current, n, m)[Current, V_ARRAY2^ANY^.bag]) {
    call update_heap(Current, V_ARRAY2^ANY^.bag, V_ARRAY2^ANY^.V_ARRAY2^ANY^.bag.static(Heap, Current)); // default:bag line:49
  }
  if (modify.V_ARRAY2^ANY^.make(Heap, Current, n, m)[Current, owns]) {
    call update_heap(Current, owns, V_ARRAY2^ANY^.owns.static(Heap, Current)); // default:owns line:49
  }
  if (*) {
    assert !(Heap[Current, observers][Current]); // type:inv tag:not_observer line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.lower_]) == (1)); // type:inv tag:lower_constraint line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Bag#Equal(Heap[Current, V_ARRAY2^ANY^.bag], Seq#ToBag(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:bag_definition line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:inv tag:array_exists line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, V_ARRAY2^ANY^.array])); // type:inv tag:owns_definition line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.lower_]) == (1); // type:inv tag:array_lower_definition line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Heap[Current, V_ARRAY2^ANY^.array], observers]); // type:inv tag:array_no_observers line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence]); // type:inv tag:sequence_implementation line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.lower_]) == (1); // type:inv tag:lower_definition line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) == (0)); // type:inv tag:column_count_empty line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (!(Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence]))) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) > (0)); // type:inv tag:column_count_nonempty line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert ((Heap[Current, V_ARRAY2^ANY^.row_count]) * (Heap[Current, V_ARRAY2^ANY^.column_count])) == (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:row_count_definition line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:49 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:49 cid:1 rid:53
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:53 line:49
}

procedure create.V_ARRAY2^ANY^.make_filled(Current: ref, n: int, m: int, v: ref);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(n); // info:type property for argument n
  free requires is_integer_32(m); // info:type property for argument m
  free requires Heap[v, allocated]; // info:type property for argument v
  modifies Heap;
  requires (((n) == (0)) && ((m) == (0))) || (((n) > (0)) && ((m) > (0))); // type:pre tag:valid_dimensions line:56
  ensures (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])) == ((n) * (m)); // type:post tag:sequence_domain_definition line:63
  ensures Seq#IsConstant(Heap[Current, V_ARRAY2^ANY^.sequence], v); // type:post tag:sequence_definition line:64
  ensures (Heap[Current, V_ARRAY2^ANY^.column_count]) == (m); // type:post tag:column_count_definition line:65
  ensures Set#IsEmpty(Heap[Current, observers]); // type:post tag:no_observers line:66
  requires (forall <T4> $f: Field T4 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.make_filled(Heap, Current, n, m, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.make_filled(old(Heap), Current, n, m, v));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



implementation create.V_ARRAY2^ANY^.make_filled(Current: ref, n: int, m: int, v: ref)
{
  var temp_3: ref;
  var temp_4: Seq (ref);

  init_locals:
  temp_3 := Void;
  temp_4 := Seq#Empty();

  entry:
  assume {:captureState "create.V_ARRAY2^ANY^.make_filled"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:58
  // row_count := n
  call update_heap(Current, V_ARRAY2^ANY^.row_count, n); // line:58
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:59
  // column_count := m
  call update_heap(Current, V_ARRAY2^ANY^.column_count, m); // line:59
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:60
  // create array.make_filled (1, n * m, v)
  call temp_3 := allocate(V_ARRAY^ANY^); // line:-1
  call create.V_ARRAY^ANY^.make_filled(temp_3, 1, (n) * (m), v); // line:60 cid:63 rid:3183
  call update_heap(Current, V_ARRAY2^ANY^.array, temp_3); // line:60
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:61
  // create sequence.constant (v, n * m)
  assert pre.fun.MML_SEQUENCE^ANY^.constant(v, (n) * (m)); // type:check tag:function_precondition line:61 cid:130 rid:3027
  call update_heap(Current, V_ARRAY2^ANY^.sequence, Seq#Constant(v, (n) * (m))); // line:61
  if (modify.V_ARRAY2^ANY^.make_filled(Heap, Current, n, m, v)[Current, V_ARRAY2^ANY^.sequence]) {
    call update_heap(Current, V_ARRAY2^ANY^.sequence, V_ARRAY2^ANY^.V_ARRAY2^ANY^.sequence.static(Heap, Current)); // default:sequence line:67
  }
  if (modify.V_ARRAY2^ANY^.make_filled(Heap, Current, n, m, v)[Current, V_ARRAY2^ANY^.lower_]) {
    call update_heap(Current, V_ARRAY2^ANY^.lower_, V_ARRAY2^ANY^.V_ARRAY2^ANY^.lower_.static(Heap, Current)); // default:lower_ line:67
  }
  if (modify.V_ARRAY2^ANY^.make_filled(Heap, Current, n, m, v)[Current, V_ARRAY2^ANY^.bag]) {
    call update_heap(Current, V_ARRAY2^ANY^.bag, V_ARRAY2^ANY^.V_ARRAY2^ANY^.bag.static(Heap, Current)); // default:bag line:67
  }
  if (modify.V_ARRAY2^ANY^.make_filled(Heap, Current, n, m, v)[Current, owns]) {
    call update_heap(Current, owns, V_ARRAY2^ANY^.owns.static(Heap, Current)); // default:owns line:67
  }
  if (*) {
    assert !(Heap[Current, observers][Current]); // type:inv tag:not_observer line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.lower_]) == (1)); // type:inv tag:lower_constraint line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Bag#Equal(Heap[Current, V_ARRAY2^ANY^.bag], Seq#ToBag(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:bag_definition line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:inv tag:array_exists line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, V_ARRAY2^ANY^.array])); // type:inv tag:owns_definition line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.lower_]) == (1); // type:inv tag:array_lower_definition line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Heap[Current, V_ARRAY2^ANY^.array], observers]); // type:inv tag:array_no_observers line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence]); // type:inv tag:sequence_implementation line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.lower_]) == (1); // type:inv tag:lower_definition line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) == (0)); // type:inv tag:column_count_empty line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (!(Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence]))) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) > (0)); // type:inv tag:column_count_nonempty line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert ((Heap[Current, V_ARRAY2^ANY^.row_count]) * (Heap[Current, V_ARRAY2^ANY^.column_count])) == (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:row_count_definition line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:67 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:67 cid:1 rid:53
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:53 line:67
}

procedure V_ARRAY2^ANY^.copy_(Current: ref, other: ref);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires detachable_exact(Heap, other, V_ARRAY2^ANY^); // info:type property for argument other
  modifies Heap;
  requires (forall i_5: ref :: (Heap[Current, observers][i_5]) ==> ((i_5) != (Void))); // type:attached tag:observers_open line:74
  requires (forall i_5: ref :: (Heap[Current, observers][i_5]) ==> (is_open(Heap, i_5))); // type:pre tag:observers_open line:74
  ensures (other) != (Void); // type:attached tag:sequence_effect line:85
  ensures Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Heap[other, V_ARRAY2^ANY^.sequence]); // type:post tag:sequence_effect line:85
  ensures (Heap[Current, V_ARRAY2^ANY^.column_count]) == (Heap[other, V_ARRAY2^ANY^.column_count]); // type:post tag:column_count_effect line:86
  ensures (forall i_6: ref :: (Heap[Current, observers][i_6]) ==> ((i_6) != (Void))); // type:attached tag:observers_open line:87
  ensures (forall i_6: ref :: (Heap[Current, observers][i_6]) ==> (is_open(Heap, i_6))); // type:post tag:observers_open line:87
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.copy_(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.copy_(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, other); // type:pre tag:arg_other_is_wrapped default:contracts
  ensures is_wrapped(Heap, other); // type:post tag:arg_other_is_wrapped default:contracts



function { :inline } variant.V_ARRAY2^ANY^.copy_.1(heap: HeapType, current: ref, other: ref) returns (ref) {
  other
}

implementation V_ARRAY2^ANY^.copy_(Current: ref, other: ref)
{
  var temp_7: ref;

  init_locals:
  temp_7 := Void;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.copy_"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:55 line:71
  assume V_ARRAY2^ANY^.user_inv(Heap, Current);
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:76
  // if other /= Current then
  if ((other) != (Current)) {
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:77
    // row_count := other.row_count
    assert {:subsumption 0} (other) != (Void); // type:attached line:77
    call update_heap(Current, V_ARRAY2^ANY^.row_count, Heap[other, V_ARRAY2^ANY^.row_count]); // line:77
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:78
    // column_count := other.column_count
    assert {:subsumption 0} (other) != (Void); // type:attached line:78
    call update_heap(Current, V_ARRAY2^ANY^.column_count, Heap[other, V_ARRAY2^ANY^.column_count]); // line:78
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:79
    // other.unwrap
    assert {:subsumption 0} (other) != (Void); // type:attached line:79
    call unwrap(other); // line:79 cid:1 rid:55
    assume user_inv(Heap, other);
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:80
    // create array.copy_ (other.array)
    call temp_7 := allocate(V_ARRAY^ANY^); // line:-1
    assert {:subsumption 0} (other) != (Void); // type:attached line:80
    call create.V_ARRAY^ANY^.copy_(temp_7, Heap[other, V_ARRAY2^ANY^.array]); // line:80 cid:63 rid:3184
    call update_heap(Current, V_ARRAY2^ANY^.array, temp_7); // line:80
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:81
    // other.wrap
    assert {:subsumption 0} (other) != (Void); // type:attached line:81
    assert {:subsumption 0} user_inv(Heap, other); // type:inv tag:unknown_invariant line:81 cid:1 rid:53
    call wrap(other); // line:81 cid:1 rid:53
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:82
    // sequence := other.sequence
    assert {:subsumption 0} (other) != (Void); // type:attached line:82
    call update_heap(Current, V_ARRAY2^ANY^.sequence, Heap[other, V_ARRAY2^ANY^.sequence]); // line:82
  }
  if (modify.V_ARRAY2^ANY^.copy_(Heap, Current, other)[Current, V_ARRAY2^ANY^.sequence]) {
    call update_heap(Current, V_ARRAY2^ANY^.sequence, V_ARRAY2^ANY^.V_ARRAY2^ANY^.sequence.static(Heap, Current)); // default:sequence line:90
  }
  if (modify.V_ARRAY2^ANY^.copy_(Heap, Current, other)[Current, V_ARRAY2^ANY^.lower_]) {
    call update_heap(Current, V_ARRAY2^ANY^.lower_, V_ARRAY2^ANY^.V_ARRAY2^ANY^.lower_.static(Heap, Current)); // default:lower_ line:90
  }
  if (modify.V_ARRAY2^ANY^.copy_(Heap, Current, other)[Current, V_ARRAY2^ANY^.bag]) {
    call update_heap(Current, V_ARRAY2^ANY^.bag, V_ARRAY2^ANY^.V_ARRAY2^ANY^.bag.static(Heap, Current)); // default:bag line:90
  }
  if (modify.V_ARRAY2^ANY^.copy_(Heap, Current, other)[Current, owns]) {
    call update_heap(Current, owns, V_ARRAY2^ANY^.owns.static(Heap, Current)); // default:owns line:90
  }
  if (*) {
    assert !(Heap[Current, observers][Current]); // type:inv tag:not_observer line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.lower_]) == (1)); // type:inv tag:lower_constraint line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Bag#Equal(Heap[Current, V_ARRAY2^ANY^.bag], Seq#ToBag(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:bag_definition line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:inv tag:array_exists line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, V_ARRAY2^ANY^.array])); // type:inv tag:owns_definition line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.lower_]) == (1); // type:inv tag:array_lower_definition line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Heap[Current, V_ARRAY2^ANY^.array], observers]); // type:inv tag:array_no_observers line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence]); // type:inv tag:sequence_implementation line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.lower_]) == (1); // type:inv tag:lower_definition line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) == (0)); // type:inv tag:column_count_empty line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (!(Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence]))) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) > (0)); // type:inv tag:column_count_nonempty line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert ((Heap[Current, V_ARRAY2^ANY^.row_count]) * (Heap[Current, V_ARRAY2^ANY^.column_count])) == (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:row_count_definition line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:90 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:90 cid:1 rid:53
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:53 line:90
}

procedure V_ARRAY2^ANY^.item(Current: ref, i: int, j: int) returns (Result: ref where Heap[Result, allocated]);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  free requires is_integer_32(j); // info:type property for argument j
  modifies Heap;
  requires fun.V_ARRAY2^ANY^.has_row(Heap, Current, i); // type:pre tag:valid_row line:97
  requires fun.V_ARRAY2^ANY^.has_column(Heap, Current, j); // type:pre tag:valid_column line:98
  ensures pre.fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j); // type:check tag:function_precondition line:103 cid:338 rid:3175
  ensures pre.fun.MML_SEQUENCE^ANY^.item(Heap[Current, V_ARRAY2^ANY^.sequence], fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j)); // type:check tag:function_precondition line:103 cid:130 rid:3031
  ensures (Result) == (Seq#Item(Heap[Current, V_ARRAY2^ANY^.sequence], fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j))); // type:post tag:definition line:103
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.item(Heap, Current, i, j), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.item(old(Heap), Current, i, j));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.item(Heap, Current, i, j), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY2^ANY^.item(old(Heap), Current, i, j));



function fun.V_ARRAY2^ANY^.item(heap: HeapType, current: ref, i: int, j: int) returns (ref);

axiom ((forall heap: HeapType, current: ref, i: int, j: int :: { fun.V_ARRAY2^ANY^.item(heap, current, i, j) } (pre.fun.V_ARRAY2^ANY^.item(heap, current, i, j)) ==> (((fun.V_ARRAY2^ANY^.item(heap, current, i, j)) == (Seq#Item(heap[current, V_ARRAY2^ANY^.sequence], fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j)))) && (heap[fun.V_ARRAY2^ANY^.item(heap, current, i, j), allocated]))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int, j: int :: { HeapSucc(h, h'), fun.V_ARRAY2^ANY^.item(h, current, i, j), fun.V_ARRAY2^ANY^.item(h', current, i, j) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.item(h, current, i, j)) && (pre.fun.V_ARRAY2^ANY^.item(h', current, i, j)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.item(h, current, i, j)))) ==> ((fun.V_ARRAY2^ANY^.item(h, current, i, j)) == (fun.V_ARRAY2^ANY^.item(h', current, i, j)))));

function { :inline } variant.V_ARRAY2^ANY^.item.1(heap: HeapType, current: ref, i: int, j: int) returns (int) {
  i
}

function { :inline } variant.V_ARRAY2^ANY^.item.2(heap: HeapType, current: ref, i: int, j: int) returns (int) {
  j
}

implementation V_ARRAY2^ANY^.item(Current: ref, i: int, j: int) returns (Result: ref)
{
  var temp_8: ref;

  init_locals:
  temp_8 := Void;
  Result := Void;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.item"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:100
  // check inv end
  assert user_inv(Heap, Current); // type:check tag:inv line:100
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:101
  // Result := flat_item (flat_index (i, j))
  assert pre.fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j); // type:check tag:function_precondition line:101 cid:338 rid:3175
  assert Frame#Subset(read.fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j), readable); // type:access tag:frame_readable line:101 cid:338 rid:3175
  assert Frame#Subset(read.fun.V_ARRAY2^ANY^.flat_item(Heap, Current, fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j)), readable); // type:access tag:frame_readable line:101 cid:338 rid:3149
  call temp_8 := V_ARRAY2^ANY^.flat_item(Current, fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j)); // line:101 cid:338 rid:3149
  Result := temp_8;
}

procedure V_ARRAY2^ANY^.flat_item(Current: ref, i: int) returns (Result: ref where Heap[Result, allocated]);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires fun.V_ARRAY2^ANY^.has_index(Heap, Current, i); // type:pre tag:has_index line:26
  ensures pre.fun.MML_SEQUENCE^ANY^.item(Heap[Current, V_ARRAY2^ANY^.sequence], ((i) - (Heap[Current, V_ARRAY2^ANY^.lower_])) + (1)); // type:check tag:function_precondition line:29 cid:130 rid:3031
  ensures (Result) == (Seq#Item(Heap[Current, V_ARRAY2^ANY^.sequence], ((i) - (Heap[Current, V_ARRAY2^ANY^.lower_])) + (1))); // type:post tag:definition line:29
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.flat_item(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.flat_item(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.flat_item(Heap, Current, i), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY2^ANY^.flat_item(old(Heap), Current, i));



function fun.V_ARRAY2^ANY^.flat_item(heap: HeapType, current: ref, i: int) returns (ref);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.flat_item(heap, current, i) } (pre.fun.V_ARRAY2^ANY^.flat_item(heap, current, i)) ==> (((fun.V_ARRAY2^ANY^.flat_item(heap, current, i)) == (Seq#Item(heap[current, V_ARRAY2^ANY^.sequence], ((i) - (heap[current, V_ARRAY2^ANY^.lower_])) + (1)))) && (heap[fun.V_ARRAY2^ANY^.flat_item(heap, current, i), allocated]))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun.V_ARRAY2^ANY^.flat_item(h, current, i), fun.V_ARRAY2^ANY^.flat_item(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.flat_item(h, current, i)) && (pre.fun.V_ARRAY2^ANY^.flat_item(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.flat_item(h, current, i)))) ==> ((fun.V_ARRAY2^ANY^.flat_item(h, current, i)) == (fun.V_ARRAY2^ANY^.flat_item(h', current, i)))));

function { :inline } variant.V_ARRAY2^ANY^.flat_item.1(heap: HeapType, current: ref, i: int) returns (int) {
  i
}

implementation V_ARRAY2^ANY^.flat_item(Current: ref, i: int) returns (Result: ref)
{
  var temp_9: ref;

  init_locals:
  temp_9 := Void;
  Result := Void;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.flat_item"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:109
  // check inv end
  assert user_inv(Heap, Current); // type:check tag:inv line:109
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:110
  // Result := array [i]
  assert readable[Current, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:110 cid:338 rid:3181
  assert {:subsumption 0} (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:attached line:110
  assert Frame#Subset(read.fun.V_ARRAY^ANY^.item(Heap, Heap[Current, V_ARRAY2^ANY^.array], i), readable); // type:access tag:frame_readable line:110 cid:63 rid:3149
  call temp_9 := V_ARRAY^ANY^.item(Heap[Current, V_ARRAY2^ANY^.array], i); // line:110 cid:63 rid:3149
  Result := temp_9;
}

procedure V_ARRAY2^ANY^.count(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  modifies Heap;
  ensures (Result) == (Bag#Card(Heap[Current, V_ARRAY2^ANY^.bag])); // type:post tag:definition line:24
  ensures (Result) == (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:post tag:definition_sequence line:82
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.count(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.count(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.count(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY2^ANY^.count(old(Heap), Current));



function fun.V_ARRAY2^ANY^.count(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY2^ANY^.count(heap, current) } (pre.fun.V_ARRAY2^ANY^.count(heap, current)) ==> (((fun.V_ARRAY2^ANY^.count(heap, current)) == (Bag#Card(heap[current, V_ARRAY2^ANY^.bag]))) && ((fun.V_ARRAY2^ANY^.count(heap, current)) == (Seq#Length(heap[current, V_ARRAY2^ANY^.sequence]))) && (is_integer_32(fun.V_ARRAY2^ANY^.count(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.V_ARRAY2^ANY^.count(h, current), fun.V_ARRAY2^ANY^.count(h', current) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.count(h, current)) && (pre.fun.V_ARRAY2^ANY^.count(h', current)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.count(h, current)))) ==> ((fun.V_ARRAY2^ANY^.count(h, current)) == (fun.V_ARRAY2^ANY^.count(h', current)))));

function { :inline } variant.V_ARRAY2^ANY^.count.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation V_ARRAY2^ANY^.count(Current: ref) returns (Result: int)
{

  init_locals:
  Result := 0;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.count"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:124
  // check inv end
  assert user_inv(Heap, Current); // type:check tag:inv line:124
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:125
  // Result := row_count * column_count
  assert readable[Current, V_ARRAY2^ANY^.row_count]; // type:access tag:attribute_readable line:125 cid:338 rid:3173
  assert readable[Current, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:125 cid:338 rid:3174
  Result := (Heap[Current, V_ARRAY2^ANY^.row_count]) * (Heap[Current, V_ARRAY2^ANY^.column_count]);
}

procedure V_ARRAY2^ANY^.flat_index(Current: ref, i: int, j: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  free requires is_integer_32(j); // info:type property for argument j
  modifies Heap;
  requires ((1) <= (i)) && ((i) <= (Heap[Current, V_ARRAY2^ANY^.row_count])); // type:pre tag:1 <= i and i <= row_count line:133
  requires ((1) <= (j)) && ((j) <= (Heap[Current, V_ARRAY2^ANY^.column_count])); // type:pre tag:1 <= j and j <= column_count line:134
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.flat_index(old(Heap), Current, i, j));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j), readable);



function fun.V_ARRAY2^ANY^.flat_index(heap: HeapType, current: ref, i: int, j: int) returns (int);

function fun0.V_ARRAY2^ANY^.flat_index(heap: HeapType, current: ref, i: int, j: int) returns (int);

axiom ((forall heap: HeapType, current: ref, i: int, j: int :: { fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j) } (pre.fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j)) ==> (is_integer_32(fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j)))));

axiom ((forall heap: HeapType, current: ref, i: int, j: int :: { fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j) } { trigger.fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j) } (pre.fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j)) ==> ((fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j)) == ((((i) - (1)) * (heap[current, V_ARRAY2^ANY^.column_count])) + (j)))));

axiom ((forall heap: HeapType, current: ref, i: int, j: int :: { fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j) } (fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j)) == (fun0.V_ARRAY2^ANY^.flat_index(heap, current, i, j))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int, j: int :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.flat_index(h, current, i, j), fun0.V_ARRAY2^ANY^.flat_index(h', current, i, j) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.flat_index(h, current, i, j)) && (pre.fun.V_ARRAY2^ANY^.flat_index(h', current, i, j)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.flat_index(h, current, i, j)))) ==> ((fun0.V_ARRAY2^ANY^.flat_index(h, current, i, j)) == (fun0.V_ARRAY2^ANY^.flat_index(h', current, i, j)))));

function { :inline } variant.V_ARRAY2^ANY^.flat_index.1(heap: HeapType, current: ref, i: int, j: int) returns (int) {
  i
}

function { :inline } variant.V_ARRAY2^ANY^.flat_index.2(heap: HeapType, current: ref, i: int, j: int) returns (int) {
  j
}

implementation V_ARRAY2^ANY^.flat_index(Current: ref, i: int, j: int) returns (Result: int)
{

  init_locals:
  Result := 0;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.flat_index"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:136
  // Result := (i - 1) * column_count + j
  assert readable[Current, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:136 cid:338 fid:104
  Result := (((i) - (1)) * (Heap[Current, V_ARRAY2^ANY^.column_count])) + (j);
}

procedure V_ARRAY2^ANY^.row_index(Current: ref, i: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires (Heap[Current, V_ARRAY2^ANY^.column_count]) > (0); // type:pre tag:non_empty line:144
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.row_index(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.row_index(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.row_index(Heap, Current, i), readable);



function fun.V_ARRAY2^ANY^.row_index(heap: HeapType, current: ref, i: int) returns (int);

function fun0.V_ARRAY2^ANY^.row_index(heap: HeapType, current: ref, i: int) returns (int);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.row_index(heap, current, i) } (pre.fun.V_ARRAY2^ANY^.row_index(heap, current, i)) ==> (is_integer_32(fun.V_ARRAY2^ANY^.row_index(heap, current, i)))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.row_index(heap, current, i) } { trigger.fun.V_ARRAY2^ANY^.row_index(heap, current, i) } (pre.fun.V_ARRAY2^ANY^.row_index(heap, current, i)) ==> ((fun.V_ARRAY2^ANY^.row_index(heap, current, i)) == ((((i) - (1)) div (heap[current, V_ARRAY2^ANY^.column_count])) + (1)))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.row_index(heap, current, i) } (fun.V_ARRAY2^ANY^.row_index(heap, current, i)) == (fun0.V_ARRAY2^ANY^.row_index(heap, current, i))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.row_index(h, current, i), fun0.V_ARRAY2^ANY^.row_index(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.row_index(h, current, i)) && (pre.fun.V_ARRAY2^ANY^.row_index(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.row_index(h, current, i)))) ==> ((fun0.V_ARRAY2^ANY^.row_index(h, current, i)) == (fun0.V_ARRAY2^ANY^.row_index(h', current, i)))));

function { :inline } variant.V_ARRAY2^ANY^.row_index.1(heap: HeapType, current: ref, i: int) returns (int) {
  i
}

implementation V_ARRAY2^ANY^.row_index(Current: ref, i: int) returns (Result: int)
{

  init_locals:
  Result := 0;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.row_index"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:146
  // Result := (i - 1) // column_count + 1
  assert readable[Current, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:146 cid:338 fid:104
  Result := (((i) - (1)) div (Heap[Current, V_ARRAY2^ANY^.column_count])) + (1);
}

procedure V_ARRAY2^ANY^.column_index(Current: ref, i: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires (Heap[Current, V_ARRAY2^ANY^.column_count]) > (0); // type:pre tag:non_empty line:154
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.column_index(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.column_index(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.column_index(Heap, Current, i), readable);



function fun.V_ARRAY2^ANY^.column_index(heap: HeapType, current: ref, i: int) returns (int);

function fun0.V_ARRAY2^ANY^.column_index(heap: HeapType, current: ref, i: int) returns (int);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.column_index(heap, current, i) } (pre.fun.V_ARRAY2^ANY^.column_index(heap, current, i)) ==> (is_integer_32(fun.V_ARRAY2^ANY^.column_index(heap, current, i)))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.column_index(heap, current, i) } { trigger.fun.V_ARRAY2^ANY^.column_index(heap, current, i) } (pre.fun.V_ARRAY2^ANY^.column_index(heap, current, i)) ==> ((fun.V_ARRAY2^ANY^.column_index(heap, current, i)) == ((((i) - (1)) mod (heap[current, V_ARRAY2^ANY^.column_count])) + (1)))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.column_index(heap, current, i) } (fun.V_ARRAY2^ANY^.column_index(heap, current, i)) == (fun0.V_ARRAY2^ANY^.column_index(heap, current, i))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.column_index(h, current, i), fun0.V_ARRAY2^ANY^.column_index(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.column_index(h, current, i)) && (pre.fun.V_ARRAY2^ANY^.column_index(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.column_index(h, current, i)))) ==> ((fun0.V_ARRAY2^ANY^.column_index(h, current, i)) == (fun0.V_ARRAY2^ANY^.column_index(h', current, i)))));

function { :inline } variant.V_ARRAY2^ANY^.column_index.1(heap: HeapType, current: ref, i: int) returns (int) {
  i
}

implementation V_ARRAY2^ANY^.column_index(Current: ref, i: int) returns (Result: int)
{

  init_locals:
  Result := 0;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.column_index"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:156
  // Result := (i - 1) \\ column_count + 1
  assert readable[Current, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:156 cid:338 fid:104
  Result := (((i) - (1)) mod (Heap[Current, V_ARRAY2^ANY^.column_count])) + (1);
}

procedure V_ARRAY2^ANY^.upper(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  modifies Heap;
  ensures (Result) == (fun.V_ARRAY2^ANY^.upper_(Heap, Current)); // type:post tag:definition line:75
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.upper(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.upper(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.upper(Heap, Current), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY2^ANY^.upper(old(Heap), Current));



function fun.V_ARRAY2^ANY^.upper(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY2^ANY^.upper(heap, current) } (pre.fun.V_ARRAY2^ANY^.upper(heap, current)) ==> (((fun.V_ARRAY2^ANY^.upper(heap, current)) == (fun.V_ARRAY2^ANY^.upper_(heap, current))) && (is_integer_32(fun.V_ARRAY2^ANY^.upper(heap, current))))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun.V_ARRAY2^ANY^.upper(h, current), fun.V_ARRAY2^ANY^.upper(h', current) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.upper(h, current)) && (pre.fun.V_ARRAY2^ANY^.upper(h', current)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.upper(h, current)))) ==> ((fun.V_ARRAY2^ANY^.upper(h, current)) == (fun.V_ARRAY2^ANY^.upper(h', current)))));

function { :inline } variant.V_ARRAY2^ANY^.upper.1(heap: HeapType, current: ref) returns (int) {
  0
}

implementation V_ARRAY2^ANY^.upper(Current: ref) returns (Result: int)
{

  init_locals:
  Result := 0;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.upper"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:165
  // check inv end
  assert user_inv(Heap, Current); // type:check tag:inv line:165
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:166
  // Result := row_count * column_count
  assert readable[Current, V_ARRAY2^ANY^.row_count]; // type:access tag:attribute_readable line:166 cid:338 rid:3173
  assert readable[Current, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:166 cid:338 rid:3174
  Result := (Heap[Current, V_ARRAY2^ANY^.row_count]) * (Heap[Current, V_ARRAY2^ANY^.column_count]);
}

procedure V_ARRAY2^ANY^.has_row(Current: ref, i: int) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.has_row(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.has_row(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.has_row(Heap, Current, i), readable);



function fun.V_ARRAY2^ANY^.has_row(heap: HeapType, current: ref, i: int) returns (bool);

function fun0.V_ARRAY2^ANY^.has_row(heap: HeapType, current: ref, i: int) returns (bool);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.has_row(heap, current, i) } { trigger.fun.V_ARRAY2^ANY^.has_row(heap, current, i) } (pre.fun.V_ARRAY2^ANY^.has_row(heap, current, i)) ==> ((fun.V_ARRAY2^ANY^.has_row(heap, current, i)) == (((1) <= (i)) && ((i) <= (heap[current, V_ARRAY2^ANY^.row_count]))))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.has_row(heap, current, i) } (fun.V_ARRAY2^ANY^.has_row(heap, current, i)) == (fun0.V_ARRAY2^ANY^.has_row(heap, current, i))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.has_row(h, current, i), fun0.V_ARRAY2^ANY^.has_row(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.has_row(h, current, i)) && (pre.fun.V_ARRAY2^ANY^.has_row(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.has_row(h, current, i)))) ==> ((fun0.V_ARRAY2^ANY^.has_row(h, current, i)) == (fun0.V_ARRAY2^ANY^.has_row(h', current, i)))));

function { :inline } variant.V_ARRAY2^ANY^.has_row.1(heap: HeapType, current: ref, i: int) returns (int) {
  i
}

implementation V_ARRAY2^ANY^.has_row(Current: ref, i: int) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.has_row"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:176
  // Result := 1 <= i and i <= row_count
  assert readable[Current, V_ARRAY2^ANY^.row_count]; // type:access tag:attribute_readable line:176 cid:338 fid:103
  Result := ((1) <= (i)) && ((i) <= (Heap[Current, V_ARRAY2^ANY^.row_count]));
}

procedure V_ARRAY2^ANY^.has_column(Current: ref, j: int) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(j); // info:type property for argument j
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.has_column(Heap, Current, j), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.has_column(old(Heap), Current, j));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.has_column(Heap, Current, j), readable);



function fun.V_ARRAY2^ANY^.has_column(heap: HeapType, current: ref, j: int) returns (bool);

function fun0.V_ARRAY2^ANY^.has_column(heap: HeapType, current: ref, j: int) returns (bool);

axiom ((forall heap: HeapType, current: ref, j: int :: { fun.V_ARRAY2^ANY^.has_column(heap, current, j) } { trigger.fun.V_ARRAY2^ANY^.has_column(heap, current, j) } (pre.fun.V_ARRAY2^ANY^.has_column(heap, current, j)) ==> ((fun.V_ARRAY2^ANY^.has_column(heap, current, j)) == (((1) <= (j)) && ((j) <= (heap[current, V_ARRAY2^ANY^.column_count]))))));

axiom ((forall heap: HeapType, current: ref, j: int :: { fun.V_ARRAY2^ANY^.has_column(heap, current, j) } (fun.V_ARRAY2^ANY^.has_column(heap, current, j)) == (fun0.V_ARRAY2^ANY^.has_column(heap, current, j))));

axiom ((forall h: HeapType, h': HeapType, current: ref, j: int :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.has_column(h, current, j), fun0.V_ARRAY2^ANY^.has_column(h', current, j) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.has_column(h, current, j)) && (pre.fun.V_ARRAY2^ANY^.has_column(h', current, j)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.has_column(h, current, j)))) ==> ((fun0.V_ARRAY2^ANY^.has_column(h, current, j)) == (fun0.V_ARRAY2^ANY^.has_column(h', current, j)))));

function { :inline } variant.V_ARRAY2^ANY^.has_column.1(heap: HeapType, current: ref, j: int) returns (int) {
  j
}

implementation V_ARRAY2^ANY^.has_column(Current: ref, j: int) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.has_column"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:184
  // Result := 1 <= j and j <= column_count
  assert readable[Current, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:184 cid:338 fid:104
  Result := ((1) <= (j)) && ((j) <= (Heap[Current, V_ARRAY2^ANY^.column_count]));
}

procedure V_ARRAY2^ANY^.flat_at(Current: ref, i: int) returns (Result: ref where detachable(Heap, Result, V_ARRAY_ITERATOR^ANY^));
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  ensures (Result) != (Void); // type:attached tag:result_fresh line:189
  ensures !(old(Heap)[Result, allocated]); // type:post tag:result_fresh line:189
  ensures (is_wrapped(Heap, Result)) && (user_inv(Heap, Result)); // type:post tag:result_wrapped line:190
  ensures Set#Equal(Heap[Current, observers], Set#Extended(old(Heap)[Current, observers], Result)); // type:post tag:result_in_observers line:191
  ensures (Heap[Result, V_ARRAY_ITERATOR^ANY^.target]) == (Current); // type:post tag:target_definition line:192
  ensures ((((Heap[Current, V_ARRAY2^ANY^.lower_]) - (1)) <= (i)) && ((i) <= ((fun.V_ARRAY2^ANY^.upper_(Heap, Current)) + (1)))) ==> ((Result) != (Void)); // type:attached tag:index_definition_in_bounds line:193
  ensures ((((Heap[Current, V_ARRAY2^ANY^.lower_]) - (1)) <= (i)) && ((i) <= ((fun.V_ARRAY2^ANY^.upper_(Heap, Current)) + (1)))) ==> ((Heap[Result, V_ARRAY_ITERATOR^ANY^.index_]) == (((i) - (Heap[Current, V_ARRAY2^ANY^.lower_])) + (1))); // type:post tag:index_definition_in_bounds line:193
  ensures ((i) < (Heap[Current, V_ARRAY2^ANY^.lower_])) ==> ((Result) != (Void)); // type:attached tag:index_definition_before line:194
  ensures ((i) < (Heap[Current, V_ARRAY2^ANY^.lower_])) ==> ((Heap[Result, V_ARRAY_ITERATOR^ANY^.index_]) == (0)); // type:post tag:index_definition_before line:194
  ensures ((i) > (fun.V_ARRAY2^ANY^.upper_(Heap, Current))) ==> ((Result) != (Void)); // type:attached tag:index_definition_after line:195
  ensures ((i) > (fun.V_ARRAY2^ANY^.upper_(Heap, Current))) ==> ((Heap[Result, V_ARRAY_ITERATOR^ANY^.index_]) == ((Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])) + (1))); // type:post tag:index_definition_after line:195
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.flat_at(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.flat_at(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.V_ARRAY2^ANY^.flat_at.1(heap: HeapType, current: ref, i: int) returns (int) {
  i
}

implementation V_ARRAY2^ANY^.flat_at(Current: ref, i: int) returns (Result: ref)
{
  var temp_10: ref;

  init_locals:
  temp_10 := Void;
  Result := Void;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.flat_at"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:194
  // check inv end
  assert user_inv(Heap, Current); // type:check tag:inv line:194
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:195
  // create Result.make (Current, i)
  call temp_10 := allocate(V_ARRAY_ITERATOR^ANY^); // line:-1
  call create.V_ARRAY_ITERATOR^ANY^.make(temp_10, Current, i); // line:195 cid:61 rid:2905
  Result := temp_10;
}

procedure V_ARRAY2^ANY^.is_equal_(Current: ref, other: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires detachable_exact(Heap, other, V_ARRAY2^ANY^); // info:type property for argument other
  modifies Heap;
  requires fun.V_ARRAY2^ANY^.is_closed_with_subjects(Heap, Current); // type:pre tag:closed_with_subjects line:410
  requires (other) != (Void); // type:attached tag:other_closed_with_subjects line:411
  requires fun.V_ARRAY2^ANY^.is_closed_with_subjects(Heap, other); // type:pre tag:other_closed_with_subjects line:411
  ensures pre.fun.V_ARRAY2^ANY^.is_model_equal(Heap, Current, other); // type:check tag:function_precondition line:415 cid:338 rid:79
  ensures (Result) == (fun.V_ARRAY2^ANY^.is_model_equal(Heap, Current, other)); // type:post tag:definition line:415
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.is_equal_(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.is_equal_(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.is_equal_(Heap, Current, other), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  requires is_closed(Heap, other); // type:pre tag:arg_other_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY2^ANY^.is_equal_(old(Heap), Current, other));



function fun.V_ARRAY2^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.V_ARRAY2^ANY^.is_equal_(heap, current, other) } (pre.fun.V_ARRAY2^ANY^.is_equal_(heap, current, other)) ==> ((fun.V_ARRAY2^ANY^.is_equal_(heap, current, other)) == (fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other)))));

axiom ((forall h: HeapType, h': HeapType, current: ref, other: ref :: { HeapSucc(h, h'), fun.V_ARRAY2^ANY^.is_equal_(h, current, other), fun.V_ARRAY2^ANY^.is_equal_(h', current, other) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.is_equal_(h, current, other)) && (pre.fun.V_ARRAY2^ANY^.is_equal_(h', current, other)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.is_equal_(h, current, other)))) ==> ((fun.V_ARRAY2^ANY^.is_equal_(h, current, other)) == (fun.V_ARRAY2^ANY^.is_equal_(h', current, other)))));

function { :inline } variant.V_ARRAY2^ANY^.is_equal_.1(heap: HeapType, current: ref, other: ref) returns (ref) {
  other
}

implementation V_ARRAY2^ANY^.is_equal_(Current: ref, other: ref) returns (Result: bool)
{
  var temp_11: bool;

  init_locals:
  temp_11 := false;
  Result := false;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.is_equal_"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:204
  // if other = Current then
  if ((other) == (Current)) {
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:205
    // Result := True
    Result := true;
  } else {
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:207
    // check inv; other.inv; array.inv; other.array.inv end
    assert user_inv(Heap, Current); // type:check tag:inv line:207
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:207
    // check inv; other.inv; array.inv; other.array.inv end
    assert {:subsumption 0} (other) != (Void); // type:attached line:207
    assert user_inv(Heap, other); // type:check tag:other.inv line:207
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:207
    // check inv; other.inv; array.inv; other.array.inv end
    assert readable[Current, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:207 cid:338 fid:117
    assert {:subsumption 0} (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:attached line:207
    assert user_inv(Heap, Heap[Current, V_ARRAY2^ANY^.array]); // type:check tag:array.inv line:207
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:207
    // check inv; other.inv; array.inv; other.array.inv end
    assert {:subsumption 0} (other) != (Void); // type:attached line:207
    assert readable[other, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:207 cid:338 fid:117
    assert {:subsumption 0} (Heap[other, V_ARRAY2^ANY^.array]) != (Void); // type:attached line:207
    assert user_inv(Heap, Heap[other, V_ARRAY2^ANY^.array]); // type:check tag:other.array.inv line:207
    // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:208
    // Result := column_count = other.column_count and array.is_equal_ (other.array)
    assert readable[Current, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:208 cid:338 rid:3174
    assert {:subsumption 0} (other) != (Void); // type:attached line:208
    assert readable[other, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:208 cid:338 rid:3174
    assert readable[Current, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:208 cid:338 rid:3181
    assert {:subsumption 0} (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:attached line:208
    assert {:subsumption 0} (other) != (Void); // type:attached line:208
    assert readable[other, V_ARRAY2^ANY^.array]; // type:access tag:attribute_readable line:208 cid:338 rid:3181
    assert Frame#Subset(read.fun.V_ARRAY^ANY^.is_equal_(Heap, Heap[Current, V_ARRAY2^ANY^.array], Heap[other, V_ARRAY2^ANY^.array]), readable); // type:access tag:frame_readable line:208 cid:63 rid:38
    call temp_11 := V_ARRAY^ANY^.is_equal_(Heap[Current, V_ARRAY2^ANY^.array], Heap[other, V_ARRAY2^ANY^.array]); // line:208 cid:63 rid:38
    Result := ((Heap[Current, V_ARRAY2^ANY^.column_count]) == (Heap[other, V_ARRAY2^ANY^.column_count])) && (temp_11);
  }
}

procedure V_ARRAY2^ANY^.put(Current: ref, v: ref, i: int, j: int);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires Heap[v, allocated]; // info:type property for argument v
  free requires is_integer_32(i); // info:type property for argument i
  free requires is_integer_32(j); // info:type property for argument j
  modifies Heap;
  requires fun.V_ARRAY2^ANY^.has_row(Heap, Current, i); // type:pre tag:valid_row line:219
  requires fun.V_ARRAY2^ANY^.has_column(Heap, Current, j); // type:pre tag:valid_column line:220
  requires (forall i_12: ref :: (Heap[Current, observers][i_12]) ==> ((i_12) != (Void))); // type:attached tag:observers_open line:221
  requires (forall i_12: ref :: (Heap[Current, observers][i_12]) ==> (is_open(Heap, i_12))); // type:pre tag:observers_open line:221
  ensures pre.fun.V_ARRAY2^ANY^.flat_index(old(Heap), Current, i, j); // type:check tag:function_precondition line:226 cid:338 rid:3175
  ensures pre.fun.MML_SEQUENCE^ANY^.replaced_at(old(Heap)[Current, V_ARRAY2^ANY^.sequence], fun.V_ARRAY2^ANY^.flat_index(old(Heap), Current, i, j), v); // type:check tag:function_precondition line:226 cid:130 rid:3053
  ensures Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Seq#Update(old(Heap)[Current, V_ARRAY2^ANY^.sequence], fun.V_ARRAY2^ANY^.flat_index(old(Heap), Current, i, j), v)); // type:post tag:sequence_effect line:226
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.put(Heap, Current, v, i, j), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.put(old(Heap), Current, v, i, j));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.V_ARRAY2^ANY^.put.1(heap: HeapType, current: ref, v: ref, i: int, j: int) returns (ref) {
  v
}

function { :inline } variant.V_ARRAY2^ANY^.put.2(heap: HeapType, current: ref, v: ref, i: int, j: int) returns (int) {
  i
}

function { :inline } variant.V_ARRAY2^ANY^.put.3(heap: HeapType, current: ref, v: ref, i: int, j: int) returns (int) {
  j
}

implementation V_ARRAY2^ANY^.put(Current: ref, v: ref, i: int, j: int)
{
  entry:
  assume {:captureState "V_ARRAY2^ANY^.put"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:223
  // check inv end
  assert user_inv(Heap, Current); // type:check tag:inv line:223
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:224
  // flat_put (v, flat_index (i, j))
  assert pre.fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j); // type:check tag:function_precondition line:224 cid:338 rid:3175
  call V_ARRAY2^ANY^.flat_put(Current, v, fun.V_ARRAY2^ANY^.flat_index(Heap, Current, i, j)); // line:224 cid:338 rid:3163
}

procedure V_ARRAY2^ANY^.flat_put(Current: ref, v: ref, i: int);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires Heap[v, allocated]; // info:type property for argument v
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires fun.V_ARRAY2^ANY^.has_index(Heap, Current, i); // type:pre tag:has_index line:39
  requires (forall i_13: ref :: (Heap[Current, observers][i_13]) ==> ((i_13) != (Void))); // type:attached tag:observers_open line:40
  requires (forall i_13: ref :: (Heap[Current, observers][i_13]) ==> (is_open(Heap, i_13))); // type:pre tag:observers_open line:40
  ensures pre.fun.MML_SEQUENCE^ANY^.replaced_at(old(Heap)[Current, V_ARRAY2^ANY^.sequence], fun.V_ARRAY2^ANY^.idx(old(Heap), Current, i), v); // type:check tag:function_precondition line:43 cid:130 rid:3053
  ensures Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Seq#Update(old(Heap)[Current, V_ARRAY2^ANY^.sequence], fun.V_ARRAY2^ANY^.idx(old(Heap), Current, i), v)); // type:post tag:sequence_effect line:43
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.flat_put(Heap, Current, v, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.flat_put(old(Heap), Current, v, i));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function { :inline } variant.V_ARRAY2^ANY^.flat_put.1(heap: HeapType, current: ref, v: ref, i: int) returns (ref) {
  v
}

function { :inline } variant.V_ARRAY2^ANY^.flat_put.2(heap: HeapType, current: ref, v: ref, i: int) returns (int) {
  i
}

implementation V_ARRAY2^ANY^.flat_put(Current: ref, v: ref, i: int)
{
  entry:
  assume {:captureState "V_ARRAY2^ANY^.flat_put"} true;
  call unwrap(Current); // default:wrapping cid:1 rid:55 line:230
  assume V_ARRAY2^ANY^.user_inv(Heap, Current);
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:233
  // array.put (v, i)
  assert {:subsumption 0} (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:attached line:233
  call V_ARRAY^ANY^.put(Heap[Current, V_ARRAY2^ANY^.array], v, i); // line:233 cid:63 rid:3163
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:234
  // sequence := sequence.replaced_at (i, v)
  assert pre.fun.MML_SEQUENCE^ANY^.replaced_at(Heap[Current, V_ARRAY2^ANY^.sequence], i, v); // type:check tag:function_precondition line:234 cid:130 rid:3053
  call update_heap(Current, V_ARRAY2^ANY^.sequence, Seq#Update(Heap[Current, V_ARRAY2^ANY^.sequence], i, v)); // line:234
  if (modify.V_ARRAY2^ANY^.flat_put(Heap, Current, v, i)[Current, V_ARRAY2^ANY^.sequence]) {
    call update_heap(Current, V_ARRAY2^ANY^.sequence, V_ARRAY2^ANY^.V_ARRAY2^ANY^.sequence.static(Heap, Current)); // default:sequence line:235
  }
  if (modify.V_ARRAY2^ANY^.flat_put(Heap, Current, v, i)[Current, V_ARRAY2^ANY^.lower_]) {
    call update_heap(Current, V_ARRAY2^ANY^.lower_, V_ARRAY2^ANY^.V_ARRAY2^ANY^.lower_.static(Heap, Current)); // default:lower_ line:235
  }
  if (modify.V_ARRAY2^ANY^.flat_put(Heap, Current, v, i)[Current, V_ARRAY2^ANY^.bag]) {
    call update_heap(Current, V_ARRAY2^ANY^.bag, V_ARRAY2^ANY^.V_ARRAY2^ANY^.bag.static(Heap, Current)); // default:bag line:235
  }
  if (modify.V_ARRAY2^ANY^.flat_put(Heap, Current, v, i)[Current, owns]) {
    call update_heap(Current, owns, V_ARRAY2^ANY^.owns.static(Heap, Current)); // default:owns line:235
  }
  if (*) {
    assert !(Heap[Current, observers][Current]); // type:inv tag:not_observer line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.lower_]) == (1)); // type:inv tag:lower_constraint line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Bag#Equal(Heap[Current, V_ARRAY2^ANY^.bag], Seq#ToBag(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:bag_definition line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.array]) != (Void); // type:inv tag:array_exists line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#Equal(Heap[Current, owns], Set#Singleton(Heap[Current, V_ARRAY2^ANY^.array])); // type:inv tag:owns_definition line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.lower_]) == (1); // type:inv tag:array_lower_definition line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Heap[Current, V_ARRAY2^ANY^.array], observers]); // type:inv tag:array_no_observers line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Heap[Heap[Current, V_ARRAY2^ANY^.array], V_ARRAY^ANY^.sequence]); // type:inv tag:sequence_implementation line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Heap[Current, V_ARRAY2^ANY^.lower_]) == (1); // type:inv tag:lower_definition line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence])) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) == (0)); // type:inv tag:column_count_empty line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert (!(Seq#IsEmpty(Heap[Current, V_ARRAY2^ANY^.sequence]))) ==> ((Heap[Current, V_ARRAY2^ANY^.column_count]) > (0)); // type:inv tag:column_count_nonempty line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert ((Heap[Current, V_ARRAY2^ANY^.row_count]) * (Heap[Current, V_ARRAY2^ANY^.column_count])) == (Seq#Length(Heap[Current, V_ARRAY2^ANY^.sequence])); // type:inv tag:row_count_definition line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert Set#IsEmpty(Heap[Current, subjects]); // type:inv tag:default_subjects line:235 cid:1 rid:53
    assume false;
  }
  if (*) {
    assert admissibility2(Heap, Current); // type:inv tag:A2 line:235 cid:1 rid:53
    assume false;
  }
  call wrap(Current); // default:wrapping cid:1 rid:53 line:235
}

procedure V_ARRAY2^ANY^.is_model_equal(Current: ref, other: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires detachable_exact(Heap, other, V_ARRAY2^ANY^); // info:type property for argument other
  modifies Heap;
  requires (other) != (Void); // type:pre tag:other /= Void line:731
  ensures ((other) == (Current)) ==> (Result); // type:post tag:reflexive line:737
  ensures (other) != (Void); // type:attached tag:symmetric line:738
  ensures pre.fun.V_ARRAY2^ANY^.is_model_equal(Heap, other, Current); // type:check tag:function_precondition line:738 cid:338 rid:79
  ensures (Result) == (fun.V_ARRAY2^ANY^.is_model_equal(Heap, other, Current)); // type:post tag:symmetric line:738
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.is_model_equal(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.is_model_equal(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.is_model_equal(Heap, Current, other), readable);



function fun.V_ARRAY2^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

function fun0.V_ARRAY2^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other) } (pre.fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other)) ==> ((((other) == (current)) ==> (fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other))) && ((fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other)) == (fun.V_ARRAY2^ANY^.is_model_equal(heap, other, current))))));

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other) } { trigger.fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other) } (pre.fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other)) ==> ((fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other)) == ((Seq#Equal(heap[current, V_ARRAY2^ANY^.sequence], heap[other, V_ARRAY2^ANY^.sequence])) && ((heap[current, V_ARRAY2^ANY^.column_count]) == (heap[other, V_ARRAY2^ANY^.column_count]))))));

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other) } (fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other)) == (fun0.V_ARRAY2^ANY^.is_model_equal(heap, current, other))));

axiom ((forall h: HeapType, h': HeapType, current: ref, other: ref :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.is_model_equal(h, current, other), fun0.V_ARRAY2^ANY^.is_model_equal(h', current, other) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.is_model_equal(h, current, other)) && (pre.fun.V_ARRAY2^ANY^.is_model_equal(h', current, other)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.is_model_equal(h, current, other)))) ==> ((fun0.V_ARRAY2^ANY^.is_model_equal(h, current, other)) == (fun0.V_ARRAY2^ANY^.is_model_equal(h', current, other)))));

function { :inline } variant.V_ARRAY2^ANY^.is_model_equal.1(heap: HeapType, current: ref, other: ref) returns (ref) {
  other
}

implementation V_ARRAY2^ANY^.is_model_equal(Current: ref, other: ref) returns (Result: bool)
{

  init_locals:
  Result := false;

  entry:
  assume {:captureState "V_ARRAY2^ANY^.is_model_equal"} true;
  // /root/es_ap/trunk/research/extension/autoproof/library/base/base2/array/v_array2.e:249
  // Result := sequence ~ other.sequence and column_count = other.column_count
  assert readable[Current, V_ARRAY2^ANY^.sequence]; // type:access tag:attribute_readable line:249 cid:338 fid:88
  assert {:subsumption 0} (other) != (Void); // type:attached line:249
  assert readable[other, V_ARRAY2^ANY^.sequence]; // type:access tag:attribute_readable line:249 cid:338 fid:88
  assert readable[Current, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:249 cid:338 fid:104
  assert {:subsumption 0} (other) != (Void); // type:attached line:249
  assert readable[other, V_ARRAY2^ANY^.column_count]; // type:access tag:attribute_readable line:249 cid:338 fid:104
  Result := (Seq#Equal(Heap[Current, V_ARRAY2^ANY^.sequence], Heap[other, V_ARRAY2^ANY^.sequence])) && ((Heap[Current, V_ARRAY2^ANY^.column_count]) == (Heap[other, V_ARRAY2^ANY^.column_count]));
}

const unique V_MUTABLE_SEQUENCE^ANY^: Type;

axiom ((V_MUTABLE_SEQUENCE^ANY^) <: (V_SEQUENCE^ANY^));

axiom ((forall t: Type :: { (V_MUTABLE_SEQUENCE^ANY^) <: (t) } ((V_MUTABLE_SEQUENCE^ANY^) <: (t)) <==> (((t) == (V_MUTABLE_SEQUENCE^ANY^)) || ((V_SEQUENCE^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_MUTABLE_SEQUENCE^ANY^)) == (-1));

axiom ((FieldId(closed, V_MUTABLE_SEQUENCE^ANY^)) == (-2));

axiom ((FieldId(owner, V_MUTABLE_SEQUENCE^ANY^)) == (-3));

axiom ((FieldId(owns, V_MUTABLE_SEQUENCE^ANY^)) == (-4));

axiom ((FieldId(observers, V_MUTABLE_SEQUENCE^ANY^)) == (-5));

axiom ((FieldId(subjects, V_MUTABLE_SEQUENCE^ANY^)) == (-6));

const V_ARRAY2^ANY^.sequence: Field (Seq (ref));

axiom ((FieldId(V_ARRAY2^ANY^.sequence, V_ARRAY2^ANY^)) == (88));

const V_MUTABLE_SEQUENCE^ANY^.sequence: Field (Seq (ref));

axiom ((V_ARRAY2^ANY^.sequence) == (V_MUTABLE_SEQUENCE^ANY^.sequence));

const V_SEQUENCE^ANY^.sequence: Field (Seq (ref));

axiom ((V_ARRAY2^ANY^.sequence) == (V_SEQUENCE^ANY^.sequence));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY2^ANY^.sequence] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY2^ANY^))) ==> (Seq#ItemsType(heap, heap[o, V_ARRAY2^ANY^.sequence], ANY))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ARRAY2^ANY^.sequence, v, o) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.sequence, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ARRAY2^ANY^.sequence, v, o) } (attached(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.sequence, v, o)) ==> (false))));

const V_ARRAY2^ANY^.column_count: Field int;

axiom ((FieldId(V_ARRAY2^ANY^.column_count, V_ARRAY2^ANY^)) == (104));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY2^ANY^.column_count] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY2^ANY^))) ==> (is_integer_32(heap[o, V_ARRAY2^ANY^.column_count]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY2^ANY^.column_count, v, o) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.column_count, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY2^ANY^.column_count, v, o) } (attached(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.column_count, v, o)) ==> (false))));

const V_ARRAY2^ANY^.lower_: Field int;

axiom ((FieldId(V_ARRAY2^ANY^.lower_, V_ARRAY2^ANY^)) == (93));

const V_MUTABLE_SEQUENCE^ANY^.lower_: Field int;

axiom ((V_ARRAY2^ANY^.lower_) == (V_MUTABLE_SEQUENCE^ANY^.lower_));

const V_SEQUENCE^ANY^.lower_: Field int;

axiom ((V_ARRAY2^ANY^.lower_) == (V_SEQUENCE^ANY^.lower_));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY2^ANY^.lower_] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY2^ANY^))) ==> (is_integer_32(heap[o, V_ARRAY2^ANY^.lower_]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY2^ANY^.lower_, v, o) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.lower_, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY2^ANY^.lower_, v, o) } (attached(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.lower_, v, o)) ==> (false))));

const V_ARRAY2^ANY^.bag: Field (Bag (ref));

axiom ((FieldId(V_ARRAY2^ANY^.bag, V_ARRAY2^ANY^)) == (78));

const V_MUTABLE_SEQUENCE^ANY^.bag: Field (Bag (ref));

axiom ((V_ARRAY2^ANY^.bag) == (V_MUTABLE_SEQUENCE^ANY^.bag));

const V_SEQUENCE^ANY^.bag: Field (Bag (ref));

axiom ((V_ARRAY2^ANY^.bag) == (V_SEQUENCE^ANY^.bag));

const V_CONTAINER^ANY^.bag: Field (Bag (ref));

axiom ((V_ARRAY2^ANY^.bag) == (V_CONTAINER^ANY^.bag));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY2^ANY^.bag] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY2^ANY^))) ==> ((Bag#DomainType(heap, heap[o, V_ARRAY2^ANY^.bag], ANY)) && (Bag#IsValid(heap[o, V_ARRAY2^ANY^.bag])))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_ARRAY2^ANY^.bag, v, o) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.bag, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_ARRAY2^ANY^.bag, v, o) } (attached(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.bag, v, o)) ==> (false))));

const V_ARRAY2^ANY^.array: Field (ref);

axiom ((FieldId(V_ARRAY2^ANY^.array, V_ARRAY2^ANY^)) == (117));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY2^ANY^.array] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY2^ANY^))) ==> (detachable_exact(heap, heap[o, V_ARRAY2^ANY^.array], V_ARRAY^ANY^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ARRAY2^ANY^.array, v, o) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.array, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ARRAY2^ANY^.array, v, o) } (attached(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.array, v, o)) ==> (false))));

const V_ARRAY^ANY^.lower_: Field int;

axiom ((FieldId(V_ARRAY^ANY^.lower_, V_ARRAY^ANY^)) == (93));

axiom ((V_ARRAY^ANY^.lower_) == (V_MUTABLE_SEQUENCE^ANY^.lower_));

axiom ((V_ARRAY^ANY^.lower_) == (V_SEQUENCE^ANY^.lower_));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^ANY^.lower_] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^ANY^))) ==> (is_integer_32(heap[o, V_ARRAY^ANY^.lower_]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^ANY^.lower_, v, o) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.lower_, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^ANY^.lower_, v, o) } (attached(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.lower_, v, o)) ==> (false))));

const V_ARRAY^ANY^.sequence: Field (Seq (ref));

axiom ((FieldId(V_ARRAY^ANY^.sequence, V_ARRAY^ANY^)) == (88));

axiom ((V_ARRAY^ANY^.sequence) == (V_MUTABLE_SEQUENCE^ANY^.sequence));

axiom ((V_ARRAY^ANY^.sequence) == (V_SEQUENCE^ANY^.sequence));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^ANY^.sequence] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^ANY^))) ==> (Seq#ItemsType(heap, heap[o, V_ARRAY^ANY^.sequence], ANY))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ARRAY^ANY^.sequence, v, o) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.sequence, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ARRAY^ANY^.sequence, v, o) } (attached(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.sequence, v, o)) ==> (false))));

const V_ARRAY2^ANY^.row_count: Field int;

axiom ((FieldId(V_ARRAY2^ANY^.row_count, V_ARRAY2^ANY^)) == (103));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY2^ANY^.row_count] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY2^ANY^))) ==> (is_integer_32(heap[o, V_ARRAY2^ANY^.row_count]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY2^ANY^.row_count, v, o) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.row_count, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY2^ANY^.row_count, v, o) } (attached(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, V_ARRAY2^ANY^.row_count, v, o)) ==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, ANY)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.ANY.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_ARRAY2^ANY^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_ARRAY2^ANY^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_ARRAY2^ANY^.in_observers(heap, current, v, o)))));

const unique V_ITERATOR^ANY^: Type;

axiom ((V_ITERATOR^ANY^) <: (V_INPUT_STREAM^ANY^));

axiom ((V_ITERATOR^ANY^) <: (ITERATION_CURSOR^ANY^));

axiom ((forall t: Type :: { (V_ITERATOR^ANY^) <: (t) } ((V_ITERATOR^ANY^) <: (t)) <==> (((t) == (V_ITERATOR^ANY^)) || ((V_INPUT_STREAM^ANY^) <: (t)) || ((ITERATION_CURSOR^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_ITERATOR^ANY^)) == (-1));

axiom ((FieldId(closed, V_ITERATOR^ANY^)) == (-2));

axiom ((FieldId(owner, V_ITERATOR^ANY^)) == (-3));

axiom ((FieldId(owns, V_ITERATOR^ANY^)) == (-4));

axiom ((FieldId(observers, V_ITERATOR^ANY^)) == (-5));

axiom ((FieldId(subjects, V_ITERATOR^ANY^)) == (-6));

axiom ((forall <T5> $f: Field T5 :: { IsModelField($f, V_ITERATOR^ANY^) } (IsModelField($f, V_ITERATOR^ANY^)) <==> ((($f) == (V_ITERATOR^ANY^.target)) || (($f) == (V_ITERATOR^ANY^.sequence)) || (($f) == (V_ITERATOR^ANY^.index_)) || (($f) == (V_ITERATOR^ANY^.box)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_ITERATOR^ANY^.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((Set#Card(heap[current, V_ITERATOR^ANY^.box])) <= (1)) && (Set#Equal(heap[current, observers], Set#Empty())) && ((heap[current, V_ITERATOR^ANY^.target]) != (Void)) && (Set#Equal(heap[current, subjects], Set#Singleton(heap[current, V_ITERATOR^ANY^.target]))) && (Bag#Equal(heap[heap[current, V_ITERATOR^ANY^.target], V_CONTAINER^ANY^.bag], Seq#ToBag(heap[current, V_ITERATOR^ANY^.sequence]))) && ((0) <= (heap[current, V_ITERATOR^ANY^.index_])) && ((heap[current, V_ITERATOR^ANY^.index_]) <= ((Seq#Length(heap[current, V_ITERATOR^ANY^.sequence])) + (1))) && (Set#Equal(heap[current, V_ITERATOR^ANY^.box], (if Seq#Domain(heap[current, V_ITERATOR^ANY^.sequence])[heap[current, V_ITERATOR^ANY^.index_]] then Set#Singleton(Seq#Item(heap[current, V_ITERATOR^ANY^.sequence], heap[current, V_ITERATOR^ANY^.index_])) else Set#Empty()))) && (admissibility2(heap, current))
}

function V_ITERATOR^ANY^.observers.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Empty()
}

function V_ITERATOR^ANY^.subjects.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, V_ITERATOR^ANY^.target])
}

function V_ITERATOR^ANY^.V_ITERATOR^ANY^.box.static(heap: HeapType, current: ref) returns (Set (ref)) {
  (if Seq#Domain(heap[current, V_ITERATOR^ANY^.sequence])[heap[current, V_ITERATOR^ANY^.index_]] then Set#Singleton(Seq#Item(heap[current, V_ITERATOR^ANY^.sequence], heap[current, V_ITERATOR^ANY^.index_])) else Set#Empty())
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_ITERATOR^ANY^)) ==> ((user_inv(heap, current)) <==> (V_ITERATOR^ANY^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_ITERATOR^ANY^)) ==> ((user_inv(heap, current)) ==> (V_ITERATOR^ANY^.user_inv(heap, current)))));

const V_ITERATOR^ANY^.target: Field (ref);

axiom ((FieldId(V_ITERATOR^ANY^.target, V_ITERATOR^ANY^)) == (79));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ITERATOR^ANY^.target] } ((IsHeap(heap)) && (attached(heap, o, V_ITERATOR^ANY^))) ==> (detachable(heap, heap[o, V_ITERATOR^ANY^.target], V_CONTAINER^ANY^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ITERATOR^ANY^.target, v, o) } (attached_exact(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ITERATOR^ANY^.target, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ITERATOR^ANY^.target, v, o) } (attached(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ITERATOR^ANY^.target, v, o)) ==> (false))));

function modify.V_ARRAY2^ANY^.forget_iterator(heap: HeapType, current: ref, it: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, it: ref :: (IsHeap(heap)) ==> ((forall <T6> $o: ref, $f: Field T6 :: { modify.V_ARRAY2^ANY^.forget_iterator(heap, current, it)[$o, $f] } (modify.V_ARRAY2^ANY^.forget_iterator(heap, current, it)[$o, $f]) <==> (((($o) == (current)) && ((($f) == (observers)) || (($f) == (closed)))) || (($o) == (it)))))));

const unique V_ARRAY_ITERATOR^ANY^: Type;

axiom ((V_ARRAY_ITERATOR^ANY^) <: (V_INDEX_ITERATOR^ANY^));

axiom ((V_ARRAY_ITERATOR^ANY^) <: (V_MUTABLE_SEQUENCE_ITERATOR^ANY^));

axiom ((forall t: Type :: { (V_ARRAY_ITERATOR^ANY^) <: (t) } ((V_ARRAY_ITERATOR^ANY^) <: (t)) <==> (((t) == (V_ARRAY_ITERATOR^ANY^)) || ((V_INDEX_ITERATOR^ANY^) <: (t)) || ((V_MUTABLE_SEQUENCE_ITERATOR^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_ARRAY_ITERATOR^ANY^)) == (-1));

axiom ((FieldId(closed, V_ARRAY_ITERATOR^ANY^)) == (-2));

axiom ((FieldId(owner, V_ARRAY_ITERATOR^ANY^)) == (-3));

axiom ((FieldId(owns, V_ARRAY_ITERATOR^ANY^)) == (-4));

axiom ((FieldId(observers, V_ARRAY_ITERATOR^ANY^)) == (-5));

axiom ((FieldId(subjects, V_ARRAY_ITERATOR^ANY^)) == (-6));

axiom ((forall <T7> $f: Field T7 :: { IsModelField($f, V_ARRAY_ITERATOR^ANY^) } (IsModelField($f, V_ARRAY_ITERATOR^ANY^)) <==> ((($f) == (V_ARRAY_ITERATOR^ANY^.target)) || (($f) == (V_ARRAY_ITERATOR^ANY^.index_)) || (($f) == (V_ARRAY_ITERATOR^ANY^.sequence)) || (($f) == (V_ARRAY_ITERATOR^ANY^.box)) || (($f) == (subjects)) || (($f) == (observers)) || (($f) == (V_ARRAY_ITERATOR^ANY^.off_)))));

function { :inline } V_ARRAY_ITERATOR^ANY^.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((Set#Card(heap[current, V_ARRAY_ITERATOR^ANY^.box])) <= (1)) && (Set#Equal(heap[current, observers], Set#Empty())) && ((heap[current, V_ARRAY_ITERATOR^ANY^.target]) != (Void)) && (Set#Equal(heap[current, subjects], Set#Singleton(heap[current, V_ARRAY_ITERATOR^ANY^.target]))) && (Bag#Equal(heap[heap[current, V_ARRAY_ITERATOR^ANY^.target], V_MUTABLE_SEQUENCE^ANY^.bag], Seq#ToBag(heap[current, V_ARRAY_ITERATOR^ANY^.sequence]))) && ((0) <= (heap[current, V_ARRAY_ITERATOR^ANY^.index_])) && ((heap[current, V_ARRAY_ITERATOR^ANY^.index_]) <= ((Seq#Length(heap[current, V_ARRAY_ITERATOR^ANY^.sequence])) + (1))) && (Set#Equal(heap[current, V_ARRAY_ITERATOR^ANY^.box], (if Seq#Domain(heap[current, V_ARRAY_ITERATOR^ANY^.sequence])[heap[current, V_ARRAY_ITERATOR^ANY^.index_]] then Set#Singleton(Seq#Item(heap[current, V_ARRAY_ITERATOR^ANY^.sequence], heap[current, V_ARRAY_ITERATOR^ANY^.index_])) else Set#Empty()))) && (Seq#Equal(heap[current, V_ARRAY_ITERATOR^ANY^.sequence], heap[heap[current, V_ARRAY_ITERATOR^ANY^.target], V_MUTABLE_SEQUENCE^ANY^.sequence])) && ((heap[current, V_ARRAY_ITERATOR^ANY^.index_]) == (heap[current, V_ARRAY_ITERATOR^ANY^.index])) && (!(heap[current, subjects][current])) && (Set#Equal(heap[current, observers], Set#Empty())) && ((heap[current, V_ARRAY_ITERATOR^ANY^.off_]) == (!(Seq#Domain(heap[current, V_ARRAY_ITERATOR^ANY^.sequence])[heap[current, V_ARRAY_ITERATOR^ANY^.index_]]))) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

function V_ARRAY_ITERATOR^ANY^.observers.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Empty()
}

function V_ARRAY_ITERATOR^ANY^.subjects.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, V_ARRAY_ITERATOR^ANY^.target])
}

function V_ARRAY_ITERATOR^ANY^.V_ARRAY_ITERATOR^ANY^.box.static(heap: HeapType, current: ref) returns (Set (ref)) {
  (if Seq#Domain(heap[current, V_ARRAY_ITERATOR^ANY^.sequence])[heap[current, V_ARRAY_ITERATOR^ANY^.index_]] then Set#Singleton(Seq#Item(heap[current, V_ARRAY_ITERATOR^ANY^.sequence], heap[current, V_ARRAY_ITERATOR^ANY^.index_])) else Set#Empty())
}

function V_ARRAY_ITERATOR^ANY^.V_ARRAY_ITERATOR^ANY^.sequence.static(heap: HeapType, current: ref) returns (Seq (ref)) {
  heap[heap[current, V_ARRAY_ITERATOR^ANY^.target], V_MUTABLE_SEQUENCE^ANY^.sequence]
}

function V_ARRAY_ITERATOR^ANY^.V_ARRAY_ITERATOR^ANY^.index_.static(heap: HeapType, current: ref) returns (int) {
  heap[current, V_ARRAY_ITERATOR^ANY^.index]
}

function V_ARRAY_ITERATOR^ANY^.V_ARRAY_ITERATOR^ANY^.off_.static(heap: HeapType, current: ref) returns (bool) {
  !(Seq#Domain(heap[current, V_ARRAY_ITERATOR^ANY^.sequence])[heap[current, V_ARRAY_ITERATOR^ANY^.index_]])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((user_inv(heap, current)) <==> (V_ARRAY_ITERATOR^ANY^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((user_inv(heap, current)) ==> (V_ARRAY_ITERATOR^ANY^.user_inv(heap, current)))));

function modify.V_ARRAY2^ANY^.add_iterator(heap: HeapType, current: ref, it: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, it: ref :: (IsHeap(heap)) ==> ((forall <T8> $o: ref, $f: Field T8 :: { modify.V_ARRAY2^ANY^.add_iterator(heap, current, it)[$o, $f] } (modify.V_ARRAY2^ANY^.add_iterator(heap, current, it)[$o, $f]) <==> ((($o) == (current)) && ((($f) == (observers)) || (($f) == (closed))))))));

function modify.V_ARRAY2^ANY^.make(heap: HeapType, current: ref, n: int, m: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: int, m: int :: (IsHeap(heap)) ==> ((forall <T9> $o: ref, $f: Field T9 :: { modify.V_ARRAY2^ANY^.make(heap, current, n, m)[$o, $f] } (modify.V_ARRAY2^ANY^.make(heap, current, n, m)[$o, $f]) <==> (($o) == (current))))));

const unique V_ARRAY^ANY^: Type;

axiom (is_frozen(V_ARRAY^ANY^));

axiom ((V_ARRAY^ANY^) <: (V_MUTABLE_SEQUENCE^ANY^));

axiom ((forall t: Type :: { (V_ARRAY^ANY^) <: (t) } ((V_ARRAY^ANY^) <: (t)) <==> (((t) == (V_ARRAY^ANY^)) || ((V_MUTABLE_SEQUENCE^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_ARRAY^ANY^)) == (-1));

axiom ((FieldId(closed, V_ARRAY^ANY^)) == (-2));

axiom ((FieldId(owner, V_ARRAY^ANY^)) == (-3));

axiom ((FieldId(owns, V_ARRAY^ANY^)) == (-4));

axiom ((FieldId(observers, V_ARRAY^ANY^)) == (-5));

axiom ((FieldId(subjects, V_ARRAY^ANY^)) == (-6));

axiom ((forall <T10> $f: Field T10 :: { IsModelField($f, V_ARRAY^ANY^) } (IsModelField($f, V_ARRAY^ANY^)) <==> ((($f) == (V_ARRAY^ANY^.sequence)) || (($f) == (V_ARRAY^ANY^.lower_)) || (($f) == (V_ARRAY^ANY^.bag)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_ARRAY^ANY^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (!(heap[current, observers][current])) && ((Seq#IsEmpty(heap[current, V_ARRAY^ANY^.sequence])) ==> ((heap[current, V_ARRAY^ANY^.lower_]) == (1))) && (Bag#Equal(heap[current, V_ARRAY^ANY^.bag], Seq#ToBag(heap[current, V_ARRAY^ANY^.sequence]))) && ((heap[current, V_ARRAY^ANY^.area]) != (Void)) && ((heap[current, V_ARRAY^ANY^.lower_]) == (heap[current, V_ARRAY^ANY^.lower])) && ((heap[current, V_ARRAY^ANY^.upper]) == (((heap[current, V_ARRAY^ANY^.lower_]) + (Seq#Length(heap[current, V_ARRAY^ANY^.sequence]))) - (1))) && (Set#Equal(heap[current, owns], Set#Singleton(heap[current, V_ARRAY^ANY^.area]))) && (Seq#Equal(heap[current, V_ARRAY^ANY^.sequence], heap[heap[current, V_ARRAY^ANY^.area], V_SPECIAL^ANY^.sequence])) && (Set#IsEmpty(heap[current, subjects])) && (admissibility2(heap, current))
}

function V_ARRAY^ANY^.V_ARRAY^ANY^.bag.static(heap: HeapType, current: ref) returns (Bag (ref)) {
  Seq#ToBag(heap[current, V_ARRAY^ANY^.sequence])
}

function V_ARRAY^ANY^.V_ARRAY^ANY^.lower_.static(heap: HeapType, current: ref) returns (int) {
  heap[current, V_ARRAY^ANY^.lower]
}

function V_ARRAY^ANY^.owns.static(heap: HeapType, current: ref) returns (Set (ref)) {
  Set#Singleton(heap[current, V_ARRAY^ANY^.area])
}

function V_ARRAY^ANY^.V_ARRAY^ANY^.sequence.static(heap: HeapType, current: ref) returns (Seq (ref)) {
  heap[heap[current, V_ARRAY^ANY^.area], V_SPECIAL^ANY^.sequence]
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((user_inv(heap, current)) <==> (V_ARRAY^ANY^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_ARRAY^ANY^)) ==> ((user_inv(heap, current)) ==> (V_ARRAY^ANY^.user_inv(heap, current)))));

procedure create.V_ARRAY^ANY^.make(Current: ref, l: int, u: int);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires is_integer_32(l); // info:type property for argument l
  free requires is_integer_32(u); // info:type property for argument u
  modifies Heap;
  requires (l) <= ((u) + (1)); // type:pre tag:valid_indexes line:38
  ensures (Seq#Length(Heap[Current, V_ARRAY^ANY^.sequence])) == (((u) - (l)) + (1)); // type:post tag:sequence_domain_definition line:49
  ensures (forall i_14: int :: (((1) <= (i_14)) && ((i_14) <= (Seq#Length(Heap[Current, V_ARRAY^ANY^.sequence])))) ==> (pre.fun.MML_SEQUENCE^ANY^.item(Heap[Current, V_ARRAY^ANY^.sequence], i_14))); // type:check tag:function_precondition line:50 cid:130 rid:3031
  ensures (forall i_14: int :: (((1) <= (i_14)) && ((i_14) <= (Seq#Length(Heap[Current, V_ARRAY^ANY^.sequence])))) ==> ((Seq#Item(Heap[Current, V_ARRAY^ANY^.sequence], i_14)) == (Void))); // type:post tag:sequence_definition line:50
  ensures (Heap[Current, V_ARRAY^ANY^.lower_]) == ((if (l) <= (u) then l else 1)); // type:post tag:lower_definition line:51
  ensures Set#IsEmpty(Heap[Current, observers]); // type:post tag:no_observers line:52
  requires (forall <T11> $f: Field T11 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.make(Heap, Current, l, u), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.make(old(Heap), Current, l, u));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function modify.V_ARRAY2^ANY^.make_filled(heap: HeapType, current: ref, n: int, m: int, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, n: int, m: int, v: ref :: (IsHeap(heap)) ==> ((forall <T12> $o: ref, $f: Field T12 :: { modify.V_ARRAY2^ANY^.make_filled(heap, current, n, m, v)[$o, $f] } (modify.V_ARRAY2^ANY^.make_filled(heap, current, n, m, v)[$o, $f]) <==> (($o) == (current))))));

procedure create.V_ARRAY^ANY^.make_filled(Current: ref, l: int, u: int, v: ref);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires is_integer_32(l); // info:type property for argument l
  free requires is_integer_32(u); // info:type property for argument u
  free requires Heap[v, allocated]; // info:type property for argument v
  modifies Heap;
  requires (l) <= ((u) + (1)); // type:pre tag:valid_indexes line:60
  ensures (Seq#Length(Heap[Current, V_ARRAY^ANY^.sequence])) == (((u) - (l)) + (1)); // type:post tag:sequence_domain_definition line:71
  ensures (forall i_15: int :: (((1) <= (i_15)) && ((i_15) <= (Seq#Length(Heap[Current, V_ARRAY^ANY^.sequence])))) ==> (pre.fun.MML_SEQUENCE^ANY^.item(Heap[Current, V_ARRAY^ANY^.sequence], i_15))); // type:check tag:function_precondition line:72 cid:130 rid:3031
  ensures (forall i_15: int :: (((1) <= (i_15)) && ((i_15) <= (Seq#Length(Heap[Current, V_ARRAY^ANY^.sequence])))) ==> ((Seq#Item(Heap[Current, V_ARRAY^ANY^.sequence], i_15)) == (v))); // type:post tag:sequence_definition line:72
  ensures (Heap[Current, V_ARRAY^ANY^.lower_]) == ((if (l) <= (u) then l else 1)); // type:post tag:lower_definition line:73
  ensures Set#IsEmpty(Heap[Current, observers]); // type:post tag:no_observers line:74
  requires (forall <T13> $f: Field T13 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.make_filled(Heap, Current, l, u, v), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.make_filled(old(Heap), Current, l, u, v));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function modify.V_ARRAY2^ANY^.copy_(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T14> $o: ref, $f: Field T14 :: { modify.V_ARRAY2^ANY^.copy_(heap, current, other)[$o, $f] } (modify.V_ARRAY2^ANY^.copy_(heap, current, other)[$o, $f]) <==> (((($o) == (other)) && (($f) == (closed))) || ((($o) == (current)) && ((!(IsModelField($f, V_ARRAY2^ANY^))) || (($f) == (V_ARRAY2^ANY^.sequence)) || (($f) == (V_ARRAY2^ANY^.bag)) || (($f) == (V_ARRAY2^ANY^.column_count)))))))));

procedure create.V_ARRAY^ANY^.copy_(Current: ref, other: ref);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires detachable_exact(Heap, other, V_ARRAY^ANY^); // info:type property for argument other
  modifies Heap;
  requires (forall i_16: ref :: (Heap[Current, observers][i_16]) ==> ((i_16) != (Void))); // type:attached tag:observers_open line:83
  requires (forall i_16: ref :: (Heap[Current, observers][i_16]) ==> (is_open(Heap, i_16))); // type:pre tag:observers_open line:83
  ensures (forall i_17: ref :: (Heap[Current, observers][i_17]) ==> ((i_17) != (Void))); // type:attached tag:observers_open line:97
  ensures (forall i_17: ref :: (Heap[Current, observers][i_17]) ==> (is_open(Heap, i_17))); // type:post tag:observers_open line:97
  ensures (other) != (Void); // type:attached tag:sequence_effect line:98
  ensures Seq#Equal(Heap[Current, V_ARRAY^ANY^.sequence], old(Heap)[other, V_ARRAY^ANY^.sequence]); // type:post tag:sequence_effect line:98
  ensures (Heap[Current, V_ARRAY^ANY^.lower_]) == (old(Heap)[other, V_ARRAY^ANY^.lower_]); // type:post tag:lower_effect line:99
  requires (forall <T15> $f: Field T15 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.copy_(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.copy_(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, other); // type:pre tag:arg_other_is_wrapped default:contracts
  ensures is_wrapped(Heap, other); // type:post tag:arg_other_is_wrapped default:contracts



procedure V_ARRAY^ANY^.copy_(Current: ref, other: ref);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires detachable_exact(Heap, other, V_ARRAY^ANY^); // info:type property for argument other
  modifies Heap;
  requires (forall i_18: ref :: (Heap[Current, observers][i_18]) ==> ((i_18) != (Void))); // type:attached tag:observers_open line:83
  requires (forall i_18: ref :: (Heap[Current, observers][i_18]) ==> (is_open(Heap, i_18))); // type:pre tag:observers_open line:83
  ensures (forall i_19: ref :: (Heap[Current, observers][i_19]) ==> ((i_19) != (Void))); // type:attached tag:observers_open line:97
  ensures (forall i_19: ref :: (Heap[Current, observers][i_19]) ==> (is_open(Heap, i_19))); // type:post tag:observers_open line:97
  ensures (other) != (Void); // type:attached tag:sequence_effect line:98
  ensures Seq#Equal(Heap[Current, V_ARRAY^ANY^.sequence], old(Heap)[other, V_ARRAY^ANY^.sequence]); // type:post tag:sequence_effect line:98
  ensures (Heap[Current, V_ARRAY^ANY^.lower_]) == (old(Heap)[other, V_ARRAY^ANY^.lower_]); // type:post tag:lower_effect line:99
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.copy_(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.copy_(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, other); // type:pre tag:arg_other_is_wrapped default:contracts
  ensures is_wrapped(Heap, other); // type:post tag:arg_other_is_wrapped default:contracts



function modify.V_ARRAY2^ANY^.item(heap: HeapType, current: ref, i: int, j: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int, j: int :: (IsHeap(heap)) ==> ((forall <T16> $o: ref, $f: Field T16 :: { modify.V_ARRAY2^ANY^.item(heap, current, i, j)[$o, $f] } (modify.V_ARRAY2^ANY^.item(heap, current, i, j)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.item(heap: HeapType, current: ref, i: int, j: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int, j: int :: (IsHeap(heap)) ==> ((forall <T17> $o: ref, $f: Field T17 :: { read.fun.V_ARRAY2^ANY^.item(heap, current, i, j)[$o, $f] } (read.fun.V_ARRAY2^ANY^.item(heap, current, i, j)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.item(heap: HeapType, current: ref, i: int, j: int) returns (bool) {
  (fun.V_ARRAY2^ANY^.has_row(heap, current, i)) && (fun.V_ARRAY2^ANY^.has_column(heap, current, j)) && (is_closed(heap, current))
}

function trigger.fun.V_ARRAY2^ANY^.item(heap: HeapType, current: ref, i: int, j: int) returns (bool);

procedure V_ARRAY2^ANY^.has_index(Current: ref, i: int) returns (Result: bool where true);
  free requires attached(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  ensures (Result) == (((Heap[Current, V_ARRAY2^ANY^.lower_]) <= (i)) && ((i) <= (fun.V_ARRAY2^ANY^.upper_(Heap, Current)))); // type:post tag:Result = (lower_ <= i and i <= upper_) line:93
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.has_index(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.has_index(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.has_index(Heap, Current, i), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY2^ANY^.has_index(old(Heap), Current, i));



function fun.V_ARRAY2^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (bool);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.has_index(heap, current, i) } (pre.fun.V_ARRAY2^ANY^.has_index(heap, current, i)) ==> ((fun.V_ARRAY2^ANY^.has_index(heap, current, i)) == (((heap[current, V_ARRAY2^ANY^.lower_]) <= (i)) && ((i) <= (fun.V_ARRAY2^ANY^.upper_(heap, current)))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun.V_ARRAY2^ANY^.has_index(h, current, i), fun.V_ARRAY2^ANY^.has_index(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.has_index(h, current, i)) && (pre.fun.V_ARRAY2^ANY^.has_index(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.has_index(h, current, i)))) ==> ((fun.V_ARRAY2^ANY^.has_index(h, current, i)) == (fun.V_ARRAY2^ANY^.has_index(h', current, i)))));

function modify.V_ARRAY2^ANY^.flat_item(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T18> $o: ref, $f: Field T18 :: { modify.V_ARRAY2^ANY^.flat_item(heap, current, i)[$o, $f] } (modify.V_ARRAY2^ANY^.flat_item(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.flat_item(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T19> $o: ref, $f: Field T19 :: { read.fun.V_ARRAY2^ANY^.flat_item(heap, current, i)[$o, $f] } (read.fun.V_ARRAY2^ANY^.flat_item(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.flat_item(heap: HeapType, current: ref, i: int) returns (bool) {
  (fun.V_ARRAY2^ANY^.has_index(heap, current, i)) && (is_closed(heap, current))
}

function trigger.fun.V_ARRAY2^ANY^.flat_item(heap: HeapType, current: ref, i: int) returns (bool);

procedure V_ARRAY^ANY^.item(Current: ref, i: int) returns (Result: ref where Heap[Result, allocated]);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires fun.V_ARRAY^ANY^.has_index(Heap, Current, i); // type:pre tag:has_index line:26
  ensures pre.fun.MML_SEQUENCE^ANY^.item(Heap[Current, V_ARRAY^ANY^.sequence], ((i) - (Heap[Current, V_ARRAY^ANY^.lower_])) + (1)); // type:check tag:function_precondition line:29 cid:130 rid:3031
  ensures (Result) == (Seq#Item(Heap[Current, V_ARRAY^ANY^.sequence], ((i) - (Heap[Current, V_ARRAY^ANY^.lower_])) + (1))); // type:post tag:definition line:29
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.item(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.item(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^ANY^.item(Heap, Current, i), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY^ANY^.item(old(Heap), Current, i));



function fun.V_ARRAY^ANY^.item(heap: HeapType, current: ref, i: int) returns (ref);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^ANY^.item(heap, current, i) } (pre.fun.V_ARRAY^ANY^.item(heap, current, i)) ==> (((fun.V_ARRAY^ANY^.item(heap, current, i)) == (Seq#Item(heap[current, V_ARRAY^ANY^.sequence], ((i) - (heap[current, V_ARRAY^ANY^.lower_])) + (1)))) && (heap[fun.V_ARRAY^ANY^.item(heap, current, i), allocated]))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun.V_ARRAY^ANY^.item(h, current, i), fun.V_ARRAY^ANY^.item(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^ANY^.item(h, current, i)) && (pre.fun.V_ARRAY^ANY^.item(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY^ANY^.item(h, current, i)))) ==> ((fun.V_ARRAY^ANY^.item(h, current, i)) == (fun.V_ARRAY^ANY^.item(h', current, i)))));

function modify.V_ARRAY2^ANY^.count(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T20> $o: ref, $f: Field T20 :: { modify.V_ARRAY2^ANY^.count(heap, current)[$o, $f] } (modify.V_ARRAY2^ANY^.count(heap, current)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.count(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T21> $o: ref, $f: Field T21 :: { read.fun.V_ARRAY2^ANY^.count(heap, current)[$o, $f] } (read.fun.V_ARRAY2^ANY^.count(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.count(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.V_ARRAY2^ANY^.count(heap: HeapType, current: ref) returns (bool);

function modify.V_ARRAY2^ANY^.flat_index(heap: HeapType, current: ref, i: int, j: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int, j: int :: (IsHeap(heap)) ==> ((forall <T22> $o: ref, $f: Field T22 :: { modify.V_ARRAY2^ANY^.flat_index(heap, current, i, j)[$o, $f] } (modify.V_ARRAY2^ANY^.flat_index(heap, current, i, j)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.flat_index(heap: HeapType, current: ref, i: int, j: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int, j: int :: (IsHeap(heap)) ==> ((forall <T23> $o: ref, $f: Field T23 :: { read.fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j)[$o, $f] } (read.fun.V_ARRAY2^ANY^.flat_index(heap, current, i, j)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.flat_index(heap: HeapType, current: ref, i: int, j: int) returns (bool) {
  ((1) <= (i)) && ((i) <= (heap[current, V_ARRAY2^ANY^.row_count])) && ((1) <= (j)) && ((j) <= (heap[current, V_ARRAY2^ANY^.column_count]))
}

function trigger.fun.V_ARRAY2^ANY^.flat_index(heap: HeapType, current: ref, i: int, j: int) returns (bool);

function modify.V_ARRAY2^ANY^.row_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T24> $o: ref, $f: Field T24 :: { modify.V_ARRAY2^ANY^.row_index(heap, current, i)[$o, $f] } (modify.V_ARRAY2^ANY^.row_index(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.row_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T25> $o: ref, $f: Field T25 :: { read.fun.V_ARRAY2^ANY^.row_index(heap, current, i)[$o, $f] } (read.fun.V_ARRAY2^ANY^.row_index(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.row_index(heap: HeapType, current: ref, i: int) returns (bool) {
  (heap[current, V_ARRAY2^ANY^.column_count]) > (0)
}

function trigger.fun.V_ARRAY2^ANY^.row_index(heap: HeapType, current: ref, i: int) returns (bool);

function modify.V_ARRAY2^ANY^.column_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T26> $o: ref, $f: Field T26 :: { modify.V_ARRAY2^ANY^.column_index(heap, current, i)[$o, $f] } (modify.V_ARRAY2^ANY^.column_index(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.column_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T27> $o: ref, $f: Field T27 :: { read.fun.V_ARRAY2^ANY^.column_index(heap, current, i)[$o, $f] } (read.fun.V_ARRAY2^ANY^.column_index(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.column_index(heap: HeapType, current: ref, i: int) returns (bool) {
  (heap[current, V_ARRAY2^ANY^.column_count]) > (0)
}

function trigger.fun.V_ARRAY2^ANY^.column_index(heap: HeapType, current: ref, i: int) returns (bool);

procedure V_ARRAY2^ANY^.upper_(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.upper_(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.upper_(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.upper_(Heap, Current), readable);



function fun.V_ARRAY2^ANY^.upper_(heap: HeapType, current: ref) returns (int);

function fun0.V_ARRAY2^ANY^.upper_(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY2^ANY^.upper_(heap, current) } (pre.fun.V_ARRAY2^ANY^.upper_(heap, current)) ==> (is_integer_32(fun.V_ARRAY2^ANY^.upper_(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY2^ANY^.upper_(heap, current) } { trigger.fun.V_ARRAY2^ANY^.upper_(heap, current) } (pre.fun.V_ARRAY2^ANY^.upper_(heap, current)) ==> ((fun.V_ARRAY2^ANY^.upper_(heap, current)) == (((heap[current, V_ARRAY2^ANY^.lower_]) + (Seq#Length(heap[current, V_ARRAY2^ANY^.sequence]))) - (1)))));

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY2^ANY^.upper_(heap, current) } (fun.V_ARRAY2^ANY^.upper_(heap, current)) == (fun0.V_ARRAY2^ANY^.upper_(heap, current))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.upper_(h, current), fun0.V_ARRAY2^ANY^.upper_(h', current) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.upper_(h, current)) && (pre.fun.V_ARRAY2^ANY^.upper_(h', current)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.upper_(h, current)))) ==> ((fun0.V_ARRAY2^ANY^.upper_(h, current)) == (fun0.V_ARRAY2^ANY^.upper_(h', current)))));

function modify.V_ARRAY2^ANY^.upper(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T28> $o: ref, $f: Field T28 :: { modify.V_ARRAY2^ANY^.upper(heap, current)[$o, $f] } (modify.V_ARRAY2^ANY^.upper(heap, current)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.upper(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T29> $o: ref, $f: Field T29 :: { read.fun.V_ARRAY2^ANY^.upper(heap, current)[$o, $f] } (read.fun.V_ARRAY2^ANY^.upper(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.upper(heap: HeapType, current: ref) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.V_ARRAY2^ANY^.upper(heap: HeapType, current: ref) returns (bool);

function modify.V_ARRAY2^ANY^.has_row(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T30> $o: ref, $f: Field T30 :: { modify.V_ARRAY2^ANY^.has_row(heap, current, i)[$o, $f] } (modify.V_ARRAY2^ANY^.has_row(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.has_row(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T31> $o: ref, $f: Field T31 :: { read.fun.V_ARRAY2^ANY^.has_row(heap, current, i)[$o, $f] } (read.fun.V_ARRAY2^ANY^.has_row(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.has_row(heap: HeapType, current: ref, i: int) returns (bool) {
  true
}

function trigger.fun.V_ARRAY2^ANY^.has_row(heap: HeapType, current: ref, i: int) returns (bool);

function modify.V_ARRAY2^ANY^.has_column(heap: HeapType, current: ref, j: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, j: int :: (IsHeap(heap)) ==> ((forall <T32> $o: ref, $f: Field T32 :: { modify.V_ARRAY2^ANY^.has_column(heap, current, j)[$o, $f] } (modify.V_ARRAY2^ANY^.has_column(heap, current, j)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.has_column(heap: HeapType, current: ref, j: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, j: int :: (IsHeap(heap)) ==> ((forall <T33> $o: ref, $f: Field T33 :: { read.fun.V_ARRAY2^ANY^.has_column(heap, current, j)[$o, $f] } (read.fun.V_ARRAY2^ANY^.has_column(heap, current, j)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.has_column(heap: HeapType, current: ref, j: int) returns (bool) {
  true
}

function trigger.fun.V_ARRAY2^ANY^.has_column(heap: HeapType, current: ref, j: int) returns (bool);

const V_ARRAY_ITERATOR^ANY^.target: Field (ref);

axiom ((FieldId(V_ARRAY_ITERATOR^ANY^.target, V_ARRAY_ITERATOR^ANY^)) == (103));

const V_INDEX_ITERATOR^ANY^.target: Field (ref);

axiom ((V_ARRAY_ITERATOR^ANY^.target) == (V_INDEX_ITERATOR^ANY^.target));

const V_SEQUENCE_ITERATOR^ANY^.target: Field (ref);

axiom ((V_ARRAY_ITERATOR^ANY^.target) == (V_SEQUENCE_ITERATOR^ANY^.target));

axiom ((V_ARRAY_ITERATOR^ANY^.target) == (V_ITERATOR^ANY^.target));

const V_MUTABLE_SEQUENCE_ITERATOR^ANY^.target: Field (ref);

axiom ((V_ARRAY_ITERATOR^ANY^.target) == (V_MUTABLE_SEQUENCE_ITERATOR^ANY^.target));

axiom ((V_ARRAY_ITERATOR^ANY^.target) == (V_SEQUENCE_ITERATOR^ANY^.target));

axiom ((V_ARRAY_ITERATOR^ANY^.target) == (V_ITERATOR^ANY^.target));

const V_IO_ITERATOR^ANY^.target: Field (ref);

axiom ((V_ARRAY_ITERATOR^ANY^.target) == (V_IO_ITERATOR^ANY^.target));

axiom ((V_ARRAY_ITERATOR^ANY^.target) == (V_ITERATOR^ANY^.target));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY_ITERATOR^ANY^.target] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY_ITERATOR^ANY^))) ==> (detachable(heap, heap[o, V_ARRAY_ITERATOR^ANY^.target], V_MUTABLE_SEQUENCE^ANY^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.target, v, o) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.target, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.target, v, o) } (attached(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.target, v, o)) ==> (false))));

const V_ARRAY_ITERATOR^ANY^.index_: Field int;

axiom ((FieldId(V_ARRAY_ITERATOR^ANY^.index_, V_ARRAY_ITERATOR^ANY^)) == (106));

const V_INDEX_ITERATOR^ANY^.index_: Field int;

axiom ((V_ARRAY_ITERATOR^ANY^.index_) == (V_INDEX_ITERATOR^ANY^.index_));

const V_SEQUENCE_ITERATOR^ANY^.index_: Field int;

axiom ((V_ARRAY_ITERATOR^ANY^.index_) == (V_SEQUENCE_ITERATOR^ANY^.index_));

const V_ITERATOR^ANY^.index_: Field int;

axiom ((V_ARRAY_ITERATOR^ANY^.index_) == (V_ITERATOR^ANY^.index_));

const V_MUTABLE_SEQUENCE_ITERATOR^ANY^.index_: Field int;

axiom ((V_ARRAY_ITERATOR^ANY^.index_) == (V_MUTABLE_SEQUENCE_ITERATOR^ANY^.index_));

axiom ((V_ARRAY_ITERATOR^ANY^.index_) == (V_SEQUENCE_ITERATOR^ANY^.index_));

axiom ((V_ARRAY_ITERATOR^ANY^.index_) == (V_ITERATOR^ANY^.index_));

const V_IO_ITERATOR^ANY^.index_: Field int;

axiom ((V_ARRAY_ITERATOR^ANY^.index_) == (V_IO_ITERATOR^ANY^.index_));

axiom ((V_ARRAY_ITERATOR^ANY^.index_) == (V_ITERATOR^ANY^.index_));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY_ITERATOR^ANY^.index_] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY_ITERATOR^ANY^))) ==> (is_integer_32(heap[o, V_ARRAY_ITERATOR^ANY^.index_]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.index_, v, o) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.index_, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.index_, v, o) } (attached(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.index_, v, o)) ==> (false))));

function modify.V_ARRAY2^ANY^.flat_at(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T34> $o: ref, $f: Field T34 :: { modify.V_ARRAY2^ANY^.flat_at(heap, current, i)[$o, $f] } (modify.V_ARRAY2^ANY^.flat_at(heap, current, i)[$o, $f]) <==> ((($o) == (current)) && ((($f) == (observers)) || (($f) == (closed))))))));

procedure create.V_ARRAY_ITERATOR^ANY^.make(Current: ref, t: ref, i: int);
  free requires attached_exact(Heap, Current, V_ARRAY_ITERATOR^ANY^); // info:type property for argument Current
  free requires detachable(Heap, t, V_MUTABLE_SEQUENCE^ANY^); // info:type property for argument t
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  ensures (Heap[Current, V_ARRAY_ITERATOR^ANY^.target]) == (t); // type:post tag:target_effect line:51
  ensures (t) != (Void); // type:attached tag:index_effect_has line:52
  ensures (((1) <= (i)) && ((i) <= (Seq#Length(Heap[t, V_MUTABLE_SEQUENCE^ANY^.sequence])))) ==> ((Heap[Current, V_ARRAY_ITERATOR^ANY^.index_]) == (i)); // type:post tag:index_effect_has line:52
  ensures ((i) < (1)) ==> ((Heap[Current, V_ARRAY_ITERATOR^ANY^.index_]) == (0)); // type:post tag:index_effect_before line:53
  ensures ((i) > (Seq#Length(Heap[t, V_MUTABLE_SEQUENCE^ANY^.sequence]))) ==> ((t) != (Void)); // type:attached tag:index_effect_after line:54
  ensures ((i) > (Seq#Length(Heap[t, V_MUTABLE_SEQUENCE^ANY^.sequence]))) ==> ((Heap[Current, V_ARRAY_ITERATOR^ANY^.index_]) == ((Seq#Length(Heap[t, V_MUTABLE_SEQUENCE^ANY^.sequence])) + (1))); // type:post tag:index_effect_after line:54
  ensures Set#Equal(Heap[t, observers], Set#Extended(old(Heap)[t, observers], Current)); // type:post tag:t_observers_effect line:55
  requires (forall <T35> $f: Field T35 :: (($f) != (allocated)) ==> ((Heap[Current, $f]) == (Default($f))));
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY_ITERATOR^ANY^.make(Heap, Current, t, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY_ITERATOR^ANY^.make(old(Heap), Current, t, i));
  free ensures HeapSucc(old(Heap), Heap);
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts
  requires is_wrapped(Heap, t); // type:pre tag:arg_t_is_wrapped default:contracts
  ensures is_wrapped(Heap, t); // type:post tag:arg_t_is_wrapped default:contracts



procedure V_ARRAY2^ANY^.is_closed_with_subjects(Current: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.is_closed_with_subjects(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.is_closed_with_subjects(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.is_closed_with_subjects(Heap, Current), readable);



function fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (bool);

function fun0.V_ARRAY2^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current) } { trigger.fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current) } (pre.fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current)) ==> ((fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current)) == ((is_closed(heap, current)) && ((forall i_20: ref :: (heap[current, subjects][i_20]) ==> (is_closed(heap, i_20))))))));

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current) } (fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current)) == (fun0.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.is_closed_with_subjects(h, current), fun0.V_ARRAY2^ANY^.is_closed_with_subjects(h', current) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.is_closed_with_subjects(h, current)) && (pre.fun.V_ARRAY2^ANY^.is_closed_with_subjects(h', current)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.is_closed_with_subjects(h, current)))) ==> ((fun0.V_ARRAY2^ANY^.is_closed_with_subjects(h, current)) == (fun0.V_ARRAY2^ANY^.is_closed_with_subjects(h', current)))));

function modify.V_ARRAY2^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T36> $o: ref, $f: Field T36 :: { modify.V_ARRAY2^ANY^.is_equal_(heap, current, other)[$o, $f] } (modify.V_ARRAY2^ANY^.is_equal_(heap, current, other)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T37> $o: ref, $f: Field T37 :: { read.fun.V_ARRAY2^ANY^.is_equal_(heap, current, other)[$o, $f] } (read.fun.V_ARRAY2^ANY^.is_equal_(heap, current, other)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (bool) {
  (fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current)) && (fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, other)) && (is_closed(heap, current)) && (is_closed(heap, other))
}

function trigger.fun.V_ARRAY2^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (bool);

procedure V_ARRAY^ANY^.is_equal_(Current: ref, other: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires detachable_exact(Heap, other, V_ARRAY^ANY^); // info:type property for argument other
  modifies Heap;
  requires fun.V_ARRAY^ANY^.is_closed_with_subjects(Heap, Current); // type:pre tag:closed_with_subjects line:410
  requires (other) != (Void); // type:attached tag:other_closed_with_subjects line:411
  requires fun.V_ARRAY^ANY^.is_closed_with_subjects(Heap, other); // type:pre tag:other_closed_with_subjects line:411
  ensures pre.fun.V_ARRAY^ANY^.is_model_equal(Heap, Current, other); // type:check tag:function_precondition line:415 cid:63 rid:79
  ensures (Result) == (fun.V_ARRAY^ANY^.is_model_equal(Heap, Current, other)); // type:post tag:definition line:415
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.is_equal_(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.is_equal_(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^ANY^.is_equal_(Heap, Current, other), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  requires is_closed(Heap, other); // type:pre tag:arg_other_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY^ANY^.is_equal_(old(Heap), Current, other));



function fun.V_ARRAY^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.V_ARRAY^ANY^.is_equal_(heap, current, other) } (pre.fun.V_ARRAY^ANY^.is_equal_(heap, current, other)) ==> ((fun.V_ARRAY^ANY^.is_equal_(heap, current, other)) == (fun.V_ARRAY^ANY^.is_model_equal(heap, current, other)))));

axiom ((forall h: HeapType, h': HeapType, current: ref, other: ref :: { HeapSucc(h, h'), fun.V_ARRAY^ANY^.is_equal_(h, current, other), fun.V_ARRAY^ANY^.is_equal_(h', current, other) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^ANY^.is_equal_(h, current, other)) && (pre.fun.V_ARRAY^ANY^.is_equal_(h', current, other)) && (same_inside(h, h', read.fun.V_ARRAY^ANY^.is_equal_(h, current, other)))) ==> ((fun.V_ARRAY^ANY^.is_equal_(h, current, other)) == (fun.V_ARRAY^ANY^.is_equal_(h', current, other)))));

function modify.V_ARRAY2^ANY^.put(heap: HeapType, current: ref, v: ref, i: int, j: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref, i: int, j: int :: (IsHeap(heap)) ==> ((forall <T38> $o: ref, $f: Field T38 :: { modify.V_ARRAY2^ANY^.put(heap, current, v, i, j)[$o, $f] } (modify.V_ARRAY2^ANY^.put(heap, current, v, i, j)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, V_ARRAY2^ANY^))) || (($f) == (V_ARRAY2^ANY^.sequence)) || (($f) == (V_ARRAY2^ANY^.bag))))))));

procedure V_ARRAY2^ANY^.idx(Current: ref, i: int) returns (Result: int where is_integer_32(Result));
  free requires attached(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  ensures (Result) == (((i) - (Heap[Current, V_ARRAY2^ANY^.lower_])) + (1)); // type:post tag:Result = i - lower_ + 1 line:232
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.idx(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.idx(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.idx(Heap, Current, i), readable);



function fun.V_ARRAY2^ANY^.idx(heap: HeapType, current: ref, i: int) returns (int);

function fun0.V_ARRAY2^ANY^.idx(heap: HeapType, current: ref, i: int) returns (int);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.idx(heap, current, i) } (pre.fun.V_ARRAY2^ANY^.idx(heap, current, i)) ==> (((fun.V_ARRAY2^ANY^.idx(heap, current, i)) == (((i) - (heap[current, V_ARRAY2^ANY^.lower_])) + (1))) && (is_integer_32(fun.V_ARRAY2^ANY^.idx(heap, current, i))))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.idx(heap, current, i) } { trigger.fun.V_ARRAY2^ANY^.idx(heap, current, i) } (pre.fun.V_ARRAY2^ANY^.idx(heap, current, i)) ==> ((fun.V_ARRAY2^ANY^.idx(heap, current, i)) == (((i) - (heap[current, V_ARRAY2^ANY^.lower_])) + (1)))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY2^ANY^.idx(heap, current, i) } (fun.V_ARRAY2^ANY^.idx(heap, current, i)) == (fun0.V_ARRAY2^ANY^.idx(heap, current, i))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.idx(h, current, i), fun0.V_ARRAY2^ANY^.idx(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.idx(h, current, i)) && (pre.fun.V_ARRAY2^ANY^.idx(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.idx(h, current, i)))) ==> ((fun0.V_ARRAY2^ANY^.idx(h, current, i)) == (fun0.V_ARRAY2^ANY^.idx(h', current, i)))));

function modify.V_ARRAY2^ANY^.flat_put(heap: HeapType, current: ref, v: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref, i: int :: (IsHeap(heap)) ==> ((forall <T39> $o: ref, $f: Field T39 :: { modify.V_ARRAY2^ANY^.flat_put(heap, current, v, i)[$o, $f] } (modify.V_ARRAY2^ANY^.flat_put(heap, current, v, i)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, V_ARRAY2^ANY^))) || (($f) == (V_ARRAY2^ANY^.sequence)) || (($f) == (V_ARRAY2^ANY^.bag))))))));

procedure V_ARRAY^ANY^.put(Current: ref, v: ref, i: int);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires Heap[v, allocated]; // info:type property for argument v
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  requires fun.V_ARRAY^ANY^.has_index(Heap, Current, i); // type:pre tag:has_index line:39
  requires (forall i_21: ref :: (Heap[Current, observers][i_21]) ==> ((i_21) != (Void))); // type:attached tag:observers_open line:40
  requires (forall i_21: ref :: (Heap[Current, observers][i_21]) ==> (is_open(Heap, i_21))); // type:pre tag:observers_open line:40
  ensures pre.fun.MML_SEQUENCE^ANY^.replaced_at(old(Heap)[Current, V_ARRAY^ANY^.sequence], fun.V_ARRAY^ANY^.idx(old(Heap), Current, i), v); // type:check tag:function_precondition line:43 cid:130 rid:3053
  ensures Seq#Equal(Heap[Current, V_ARRAY^ANY^.sequence], Seq#Update(old(Heap)[Current, V_ARRAY^ANY^.sequence], fun.V_ARRAY^ANY^.idx(old(Heap), Current, i), v)); // type:post tag:sequence_effect line:43
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.put(Heap, Current, v, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.put(old(Heap), Current, v, i));
  free ensures HeapSucc(old(Heap), Heap);
  requires is_wrapped(Heap, Current); // type:pre tag:default_is_wrapped default:contracts
  ensures is_wrapped(Heap, Current); // type:post tag:default_is_wrapped default:contracts



function modify.V_ARRAY2^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T40> $o: ref, $f: Field T40 :: { modify.V_ARRAY2^ANY^.is_model_equal(heap, current, other)[$o, $f] } (modify.V_ARRAY2^ANY^.is_model_equal(heap, current, other)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T41> $o: ref, $f: Field T41 :: { read.fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other)[$o, $f] } (read.fun.V_ARRAY2^ANY^.is_model_equal(heap, current, other)[$o, $f]) <==> (((($o) == (current)) || (($o) == (other))) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool) {
  (other) != (Void)
}

function trigger.fun.V_ARRAY2^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

const unique V_SEQUENCE^ANY^: Type;

axiom ((V_SEQUENCE^ANY^) <: (V_CONTAINER^ANY^));

axiom ((forall t: Type :: { (V_SEQUENCE^ANY^) <: (t) } ((V_SEQUENCE^ANY^) <: (t)) <==> (((t) == (V_SEQUENCE^ANY^)) || ((V_CONTAINER^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_SEQUENCE^ANY^)) == (-1));

axiom ((FieldId(closed, V_SEQUENCE^ANY^)) == (-2));

axiom ((FieldId(owner, V_SEQUENCE^ANY^)) == (-3));

axiom ((FieldId(owns, V_SEQUENCE^ANY^)) == (-4));

axiom ((FieldId(observers, V_SEQUENCE^ANY^)) == (-5));

axiom ((FieldId(subjects, V_SEQUENCE^ANY^)) == (-6));

const unique V_CONTAINER^ANY^: Type;

axiom ((V_CONTAINER^ANY^) <: (ITERABLE^ANY^));

axiom ((forall t: Type :: { (V_CONTAINER^ANY^) <: (t) } ((V_CONTAINER^ANY^) <: (t)) <==> (((t) == (V_CONTAINER^ANY^)) || ((ITERABLE^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_CONTAINER^ANY^)) == (-1));

axiom ((FieldId(closed, V_CONTAINER^ANY^)) == (-2));

axiom ((FieldId(owner, V_CONTAINER^ANY^)) == (-3));

axiom ((FieldId(owns, V_CONTAINER^ANY^)) == (-4));

axiom ((FieldId(observers, V_CONTAINER^ANY^)) == (-5));

axiom ((FieldId(subjects, V_CONTAINER^ANY^)) == (-6));

procedure ANY.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, ANY); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free requires global_permissive();
  free ensures global(Heap);
  requires Frame#Subset(modify.ANY.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.ANY.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.ANY.in_observers(Heap, Current, new_observers, o), readable);



function fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ANY.in_observers(heap, current, new_observers, o) } { trigger.fun.ANY.in_observers(heap, current, new_observers, o) } (pre.fun.ANY.in_observers(heap, current, new_observers, o)) ==> ((fun.ANY.in_observers(heap, current, new_observers, o)) == ((attached(heap, o, ANY)) && (new_observers[o])))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.ANY.in_observers(heap, current, new_observers, o) } (fun.ANY.in_observers(heap, current, new_observers, o)) == (fun0.ANY.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.ANY.in_observers(h, current, new_observers, o), fun0.ANY.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.ANY.in_observers(h, current, new_observers, o)) && (pre.fun.ANY.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.ANY.in_observers(h, current, new_observers, o)))) ==> ((fun0.ANY.in_observers(h, current, new_observers, o)) == (fun0.ANY.in_observers(h', current, new_observers, o)))));

procedure V_ARRAY2^ANY^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY2^ANY^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY2^ANY^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY2^ANY^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY2^ANY^.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_ARRAY2^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_ARRAY2^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o) } { trigger.fun.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o) } (pre.fun.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o)) ==> ((fun.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o)) == ((attached(heap, o, ANY)) && (new_observers[o])))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o) } (fun.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o)) == (fun0.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_ARRAY2^ANY^.in_observers(h, current, new_observers, o), fun0.V_ARRAY2^ANY^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY2^ANY^.in_observers(h, current, new_observers, o)) && (pre.fun.V_ARRAY2^ANY^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_ARRAY2^ANY^.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_ARRAY2^ANY^.in_observers(h, current, new_observers, o)) == (fun0.V_ARRAY2^ANY^.in_observers(h', current, new_observers, o)))));

const unique V_INPUT_STREAM^ANY^: Type;

axiom ((V_INPUT_STREAM^ANY^) <: (ANY));

axiom ((forall t: Type :: { (V_INPUT_STREAM^ANY^) <: (t) } ((V_INPUT_STREAM^ANY^) <: (t)) <==> (((t) == (V_INPUT_STREAM^ANY^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, V_INPUT_STREAM^ANY^)) == (-1));

axiom ((FieldId(closed, V_INPUT_STREAM^ANY^)) == (-2));

axiom ((FieldId(owner, V_INPUT_STREAM^ANY^)) == (-3));

axiom ((FieldId(owns, V_INPUT_STREAM^ANY^)) == (-4));

axiom ((FieldId(observers, V_INPUT_STREAM^ANY^)) == (-5));

axiom ((FieldId(subjects, V_INPUT_STREAM^ANY^)) == (-6));

const unique ITERATION_CURSOR^ANY^: Type;

axiom ((ITERATION_CURSOR^ANY^) <: (ANY));

axiom ((forall t: Type :: { (ITERATION_CURSOR^ANY^) <: (t) } ((ITERATION_CURSOR^ANY^) <: (t)) <==> (((t) == (ITERATION_CURSOR^ANY^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, ITERATION_CURSOR^ANY^)) == (-1));

axiom ((FieldId(closed, ITERATION_CURSOR^ANY^)) == (-2));

axiom ((FieldId(owner, ITERATION_CURSOR^ANY^)) == (-3));

axiom ((FieldId(owns, ITERATION_CURSOR^ANY^)) == (-4));

axiom ((FieldId(observers, ITERATION_CURSOR^ANY^)) == (-5));

axiom ((FieldId(subjects, ITERATION_CURSOR^ANY^)) == (-6));

const V_ITERATOR^ANY^.sequence: Field (Seq (ref));

axiom ((FieldId(V_ITERATOR^ANY^.sequence, V_ITERATOR^ANY^)) == (97));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ITERATOR^ANY^.sequence] } ((IsHeap(heap)) && (attached(heap, o, V_ITERATOR^ANY^))) ==> (Seq#ItemsType(heap, heap[o, V_ITERATOR^ANY^.sequence], ANY))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ITERATOR^ANY^.sequence, v, o) } (attached_exact(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ITERATOR^ANY^.sequence, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ITERATOR^ANY^.sequence, v, o) } (attached(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ITERATOR^ANY^.sequence, v, o)) ==> (false))));

axiom ((FieldId(V_ITERATOR^ANY^.index_, V_ITERATOR^ANY^)) == (98));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ITERATOR^ANY^.index_] } ((IsHeap(heap)) && (attached(heap, o, V_ITERATOR^ANY^))) ==> (is_integer_32(heap[o, V_ITERATOR^ANY^.index_]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ITERATOR^ANY^.index_, v, o) } (attached_exact(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ITERATOR^ANY^.index_, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ITERATOR^ANY^.index_, v, o) } (attached(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ITERATOR^ANY^.index_, v, o)) ==> (false))));

const V_ITERATOR^ANY^.box: Field (Set (ref));

axiom ((FieldId(V_ITERATOR^ANY^.box, V_ITERATOR^ANY^)) == (78));

const V_INPUT_STREAM^ANY^.box: Field (Set (ref));

axiom ((V_ITERATOR^ANY^.box) == (V_INPUT_STREAM^ANY^.box));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ITERATOR^ANY^.box] } ((IsHeap(heap)) && (attached(heap, o, V_ITERATOR^ANY^))) ==> (Set#ItemsType(heap, heap[o, V_ITERATOR^ANY^.box], ANY))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, V_ITERATOR^ANY^.box, v, o) } (attached_exact(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ITERATOR^ANY^.box, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, V_ITERATOR^ANY^.box, v, o) } (attached(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ITERATOR^ANY^.box, v, o)) ==> (false))));

axiom ((FieldId(V_CONTAINER^ANY^.bag, V_CONTAINER^ANY^)) == (83));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_CONTAINER^ANY^.bag] } ((IsHeap(heap)) && (attached(heap, o, V_CONTAINER^ANY^))) ==> ((Bag#DomainType(heap, heap[o, V_CONTAINER^ANY^.bag], ANY)) && (Bag#IsValid(heap[o, V_CONTAINER^ANY^.bag])))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_CONTAINER^ANY^.bag, v, o) } (attached_exact(heap, current, V_CONTAINER^ANY^)) ==> ((guard(heap, current, V_CONTAINER^ANY^.bag, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_CONTAINER^ANY^.bag, v, o) } (attached(heap, current, V_CONTAINER^ANY^)) ==> ((guard(heap, current, V_CONTAINER^ANY^.bag, v, o)) ==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_ITERATOR^ANY^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_ITERATOR^ANY^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_ITERATOR^ANY^.in_observers(heap, current, v, o)))));

axiom ((forall <T42> $f: Field T42 :: { IsModelField($f, V_CONTAINER^ANY^) } (IsModelField($f, V_CONTAINER^ANY^)) <==> ((($f) == (V_CONTAINER^ANY^.bag)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_CONTAINER^ANY^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (!(heap[current, observers][current])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_CONTAINER^ANY^)) ==> ((user_inv(heap, current)) <==> (V_CONTAINER^ANY^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_CONTAINER^ANY^)) ==> ((user_inv(heap, current)) ==> (V_CONTAINER^ANY^.user_inv(heap, current)))));

const unique V_INDEX_ITERATOR^ANY^: Type;

axiom ((V_INDEX_ITERATOR^ANY^) <: (V_SEQUENCE_ITERATOR^ANY^));

axiom ((forall t: Type :: { (V_INDEX_ITERATOR^ANY^) <: (t) } ((V_INDEX_ITERATOR^ANY^) <: (t)) <==> (((t) == (V_INDEX_ITERATOR^ANY^)) || ((V_SEQUENCE_ITERATOR^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_INDEX_ITERATOR^ANY^)) == (-1));

axiom ((FieldId(closed, V_INDEX_ITERATOR^ANY^)) == (-2));

axiom ((FieldId(owner, V_INDEX_ITERATOR^ANY^)) == (-3));

axiom ((FieldId(owns, V_INDEX_ITERATOR^ANY^)) == (-4));

axiom ((FieldId(observers, V_INDEX_ITERATOR^ANY^)) == (-5));

axiom ((FieldId(subjects, V_INDEX_ITERATOR^ANY^)) == (-6));

const unique V_MUTABLE_SEQUENCE_ITERATOR^ANY^: Type;

axiom ((V_MUTABLE_SEQUENCE_ITERATOR^ANY^) <: (V_SEQUENCE_ITERATOR^ANY^));

axiom ((V_MUTABLE_SEQUENCE_ITERATOR^ANY^) <: (V_IO_ITERATOR^ANY^));

axiom ((forall t: Type :: { (V_MUTABLE_SEQUENCE_ITERATOR^ANY^) <: (t) } ((V_MUTABLE_SEQUENCE_ITERATOR^ANY^) <: (t)) <==> (((t) == (V_MUTABLE_SEQUENCE_ITERATOR^ANY^)) || ((V_SEQUENCE_ITERATOR^ANY^) <: (t)) || ((V_IO_ITERATOR^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_MUTABLE_SEQUENCE_ITERATOR^ANY^)) == (-1));

axiom ((FieldId(closed, V_MUTABLE_SEQUENCE_ITERATOR^ANY^)) == (-2));

axiom ((FieldId(owner, V_MUTABLE_SEQUENCE_ITERATOR^ANY^)) == (-3));

axiom ((FieldId(owns, V_MUTABLE_SEQUENCE_ITERATOR^ANY^)) == (-4));

axiom ((FieldId(observers, V_MUTABLE_SEQUENCE_ITERATOR^ANY^)) == (-5));

axiom ((FieldId(subjects, V_MUTABLE_SEQUENCE_ITERATOR^ANY^)) == (-6));

const V_ARRAY_ITERATOR^ANY^.sequence: Field (Seq (ref));

axiom ((FieldId(V_ARRAY_ITERATOR^ANY^.sequence, V_ARRAY_ITERATOR^ANY^)) == (105));

const V_INDEX_ITERATOR^ANY^.sequence: Field (Seq (ref));

axiom ((V_ARRAY_ITERATOR^ANY^.sequence) == (V_INDEX_ITERATOR^ANY^.sequence));

const V_SEQUENCE_ITERATOR^ANY^.sequence: Field (Seq (ref));

axiom ((V_ARRAY_ITERATOR^ANY^.sequence) == (V_SEQUENCE_ITERATOR^ANY^.sequence));

axiom ((V_ARRAY_ITERATOR^ANY^.sequence) == (V_ITERATOR^ANY^.sequence));

const V_MUTABLE_SEQUENCE_ITERATOR^ANY^.sequence: Field (Seq (ref));

axiom ((V_ARRAY_ITERATOR^ANY^.sequence) == (V_MUTABLE_SEQUENCE_ITERATOR^ANY^.sequence));

axiom ((V_ARRAY_ITERATOR^ANY^.sequence) == (V_SEQUENCE_ITERATOR^ANY^.sequence));

axiom ((V_ARRAY_ITERATOR^ANY^.sequence) == (V_ITERATOR^ANY^.sequence));

const V_IO_ITERATOR^ANY^.sequence: Field (Seq (ref));

axiom ((V_ARRAY_ITERATOR^ANY^.sequence) == (V_IO_ITERATOR^ANY^.sequence));

axiom ((V_ARRAY_ITERATOR^ANY^.sequence) == (V_ITERATOR^ANY^.sequence));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY_ITERATOR^ANY^.sequence] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY_ITERATOR^ANY^))) ==> (Seq#ItemsType(heap, heap[o, V_ARRAY_ITERATOR^ANY^.sequence], ANY))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.sequence, v, o) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.sequence, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.sequence, v, o) } (attached(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.sequence, v, o)) ==> (false))));

const V_ARRAY_ITERATOR^ANY^.box: Field (Set (ref));

axiom ((FieldId(V_ARRAY_ITERATOR^ANY^.box, V_ARRAY_ITERATOR^ANY^)) == (76));

const V_INDEX_ITERATOR^ANY^.box: Field (Set (ref));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_INDEX_ITERATOR^ANY^.box));

const V_SEQUENCE_ITERATOR^ANY^.box: Field (Set (ref));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_SEQUENCE_ITERATOR^ANY^.box));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_ITERATOR^ANY^.box));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_INPUT_STREAM^ANY^.box));

const V_MUTABLE_SEQUENCE_ITERATOR^ANY^.box: Field (Set (ref));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_MUTABLE_SEQUENCE_ITERATOR^ANY^.box));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_SEQUENCE_ITERATOR^ANY^.box));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_ITERATOR^ANY^.box));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_INPUT_STREAM^ANY^.box));

const V_IO_ITERATOR^ANY^.box: Field (Set (ref));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_IO_ITERATOR^ANY^.box));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_ITERATOR^ANY^.box));

axiom ((V_ARRAY_ITERATOR^ANY^.box) == (V_INPUT_STREAM^ANY^.box));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY_ITERATOR^ANY^.box] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY_ITERATOR^ANY^))) ==> (Set#ItemsType(heap, heap[o, V_ARRAY_ITERATOR^ANY^.box], ANY))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.box, v, o) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.box, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.box, v, o) } (attached(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.box, v, o)) ==> (false))));

const V_ARRAY_ITERATOR^ANY^.off_: Field bool;

axiom ((FieldId(V_ARRAY_ITERATOR^ANY^.off_, V_ARRAY_ITERATOR^ANY^)) == (87));

const V_MUTABLE_SEQUENCE_ITERATOR^ANY^.off_: Field bool;

axiom ((V_ARRAY_ITERATOR^ANY^.off_) == (V_MUTABLE_SEQUENCE_ITERATOR^ANY^.off_));

const V_IO_ITERATOR^ANY^.off_: Field bool;

axiom ((V_ARRAY_ITERATOR^ANY^.off_) == (V_IO_ITERATOR^ANY^.off_));

const V_OUTPUT_STREAM^ANY^.off_: Field bool;

axiom ((V_ARRAY_ITERATOR^ANY^.off_) == (V_OUTPUT_STREAM^ANY^.off_));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.off_, v, o) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.off_, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: bool, o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.off_, v, o) } (attached(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.off_, v, o)) ==> (false))));

axiom ((FieldId(V_MUTABLE_SEQUENCE^ANY^.bag, V_MUTABLE_SEQUENCE^ANY^)) == (80));

axiom ((V_MUTABLE_SEQUENCE^ANY^.bag) == (V_SEQUENCE^ANY^.bag));

axiom ((V_MUTABLE_SEQUENCE^ANY^.bag) == (V_CONTAINER^ANY^.bag));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_MUTABLE_SEQUENCE^ANY^.bag] } ((IsHeap(heap)) && (attached(heap, o, V_MUTABLE_SEQUENCE^ANY^))) ==> ((Bag#DomainType(heap, heap[o, V_MUTABLE_SEQUENCE^ANY^.bag], ANY)) && (Bag#IsValid(heap[o, V_MUTABLE_SEQUENCE^ANY^.bag])))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.bag, v, o) } (attached_exact(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.bag, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.bag, v, o) } (attached(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.bag, v, o)) ==> (false))));

axiom ((FieldId(V_MUTABLE_SEQUENCE^ANY^.sequence, V_MUTABLE_SEQUENCE^ANY^)) == (92));

axiom ((V_MUTABLE_SEQUENCE^ANY^.sequence) == (V_SEQUENCE^ANY^.sequence));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_MUTABLE_SEQUENCE^ANY^.sequence] } ((IsHeap(heap)) && (attached(heap, o, V_MUTABLE_SEQUENCE^ANY^))) ==> (Seq#ItemsType(heap, heap[o, V_MUTABLE_SEQUENCE^ANY^.sequence], ANY))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.sequence, v, o) } (attached_exact(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.sequence, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.sequence, v, o) } (attached(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.sequence, v, o)) ==> (false))));

const V_ARRAY_ITERATOR^ANY^.index: Field int;

axiom ((FieldId(V_ARRAY_ITERATOR^ANY^.index, V_ARRAY_ITERATOR^ANY^)) == (84));

const V_INDEX_ITERATOR^ANY^.index: Field int;

axiom ((V_ARRAY_ITERATOR^ANY^.index) == (V_INDEX_ITERATOR^ANY^.index));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY_ITERATOR^ANY^.index] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY_ITERATOR^ANY^))) ==> (is_integer_32(heap[o, V_ARRAY_ITERATOR^ANY^.index]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.index, v, o) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.index, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY_ITERATOR^ANY^.index, v, o) } (attached(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, V_ARRAY_ITERATOR^ANY^.index, v, o)) ==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_ARRAY_ITERATOR^ANY^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, v, o)))));

const V_ARRAY^ANY^.bag: Field (Bag (ref));

axiom ((FieldId(V_ARRAY^ANY^.bag, V_ARRAY^ANY^)) == (78));

axiom ((V_ARRAY^ANY^.bag) == (V_MUTABLE_SEQUENCE^ANY^.bag));

axiom ((V_ARRAY^ANY^.bag) == (V_SEQUENCE^ANY^.bag));

axiom ((V_ARRAY^ANY^.bag) == (V_CONTAINER^ANY^.bag));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^ANY^.bag] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^ANY^))) ==> ((Bag#DomainType(heap, heap[o, V_ARRAY^ANY^.bag], ANY)) && (Bag#IsValid(heap[o, V_ARRAY^ANY^.bag])))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_ARRAY^ANY^.bag, v, o) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.bag, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Bag (ref), o: ref :: { guard(heap, current, V_ARRAY^ANY^.bag, v, o) } (attached(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.bag, v, o)) ==> (false))));

const V_ARRAY^ANY^.area: Field (ref);

axiom ((FieldId(V_ARRAY^ANY^.area, V_ARRAY^ANY^)) == (114));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^ANY^.area] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^ANY^))) ==> (detachable(heap, heap[o, V_ARRAY^ANY^.area], V_SPECIAL^ANY^))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ARRAY^ANY^.area, v, o) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.area, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: ref, o: ref :: { guard(heap, current, V_ARRAY^ANY^.area, v, o) } (attached(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.area, v, o)) ==> (false))));

const V_ARRAY^ANY^.lower: Field int;

axiom ((FieldId(V_ARRAY^ANY^.lower, V_ARRAY^ANY^)) == (101));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^ANY^.lower] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^ANY^))) ==> (is_integer_32(heap[o, V_ARRAY^ANY^.lower]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^ANY^.lower, v, o) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.lower, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^ANY^.lower, v, o) } (attached(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.lower, v, o)) ==> (false))));

const V_ARRAY^ANY^.upper: Field int;

axiom ((FieldId(V_ARRAY^ANY^.upper, V_ARRAY^ANY^)) == (102));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_ARRAY^ANY^.upper] } ((IsHeap(heap)) && (attached(heap, o, V_ARRAY^ANY^))) ==> (is_integer_32(heap[o, V_ARRAY^ANY^.upper]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^ANY^.upper, v, o) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.upper, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_ARRAY^ANY^.upper, v, o) } (attached(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, V_ARRAY^ANY^.upper, v, o)) ==> (false))));

const V_SPECIAL^ANY^.sequence: Field (Seq (ref));

axiom ((FieldId(V_SPECIAL^ANY^.sequence, V_SPECIAL^ANY^)) == (94));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_SPECIAL^ANY^.sequence] } ((IsHeap(heap)) && (attached(heap, o, V_SPECIAL^ANY^))) ==> (Seq#ItemsType(heap, heap[o, V_SPECIAL^ANY^.sequence], ANY))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_SPECIAL^ANY^.sequence, v, o) } (attached_exact(heap, current, V_SPECIAL^ANY^)) ==> ((guard(heap, current, V_SPECIAL^ANY^.sequence, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Seq (ref), o: ref :: { guard(heap, current, V_SPECIAL^ANY^.sequence, v, o) } (attached(heap, current, V_SPECIAL^ANY^)) ==> ((guard(heap, current, V_SPECIAL^ANY^.sequence, v, o)) ==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_ARRAY^ANY^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_ARRAY^ANY^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_ARRAY^ANY^.in_observers(heap, current, v, o)))));

function modify.V_ARRAY^ANY^.make(heap: HeapType, current: ref, l: int, u: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, l: int, u: int :: (IsHeap(heap)) ==> ((forall <T43> $o: ref, $f: Field T43 :: { modify.V_ARRAY^ANY^.make(heap, current, l, u)[$o, $f] } (modify.V_ARRAY^ANY^.make(heap, current, l, u)[$o, $f]) <==> (($o) == (current))))));

function pre.fun.MML_SEQUENCE^ANY^.constant(x: ref, n: int) returns (bool) {
  (n) >= (0)
}

function trigger.fun.MML_SEQUENCE^ANY^.constant(x: ref, n: int) returns (bool);

function modify.V_ARRAY^ANY^.make_filled(heap: HeapType, current: ref, l: int, u: int, v: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, l: int, u: int, v: ref :: (IsHeap(heap)) ==> ((forall <T44> $o: ref, $f: Field T44 :: { modify.V_ARRAY^ANY^.make_filled(heap, current, l, u, v)[$o, $f] } (modify.V_ARRAY^ANY^.make_filled(heap, current, l, u, v)[$o, $f]) <==> (($o) == (current))))));

function modify.V_ARRAY^ANY^.copy_(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T45> $o: ref, $f: Field T45 :: { modify.V_ARRAY^ANY^.copy_(heap, current, other)[$o, $f] } (modify.V_ARRAY^ANY^.copy_(heap, current, other)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, V_ARRAY^ANY^))) || (($f) == (V_ARRAY^ANY^.sequence)) || (($f) == (V_ARRAY^ANY^.bag)) || (($f) == (V_ARRAY^ANY^.lower_))))))));

function pre.fun.MML_SEQUENCE^ANY^.item(current: Seq (ref), i: int) returns (bool) {
  ((1) <= (i)) && ((i) <= (Seq#Length(current)))
}

function trigger.fun.MML_SEQUENCE^ANY^.item(current: Seq (ref), i: int) returns (bool);

function modify.V_ARRAY2^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T46> $o: ref, $f: Field T46 :: { modify.V_ARRAY2^ANY^.has_index(heap, current, i)[$o, $f] } (modify.V_ARRAY2^ANY^.has_index(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T47> $o: ref, $f: Field T47 :: { read.fun.V_ARRAY2^ANY^.has_index(heap, current, i)[$o, $f] } (read.fun.V_ARRAY2^ANY^.has_index(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.V_ARRAY2^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (bool);

procedure V_ARRAY^ANY^.has_index(Current: ref, i: int) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  ensures (Result) == (((Heap[Current, V_ARRAY^ANY^.lower_]) <= (i)) && ((i) <= (fun.V_ARRAY^ANY^.upper_(Heap, Current)))); // type:post tag:Result = (lower_ <= i and i <= upper_) line:93
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.has_index(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.has_index(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^ANY^.has_index(Heap, Current, i), readable);
  requires is_closed(Heap, Current); // type:pre tag:default_is_closed default:contracts
  free ensures (Result) == (fun.V_ARRAY^ANY^.has_index(old(Heap), Current, i));



function fun.V_ARRAY^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (bool);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^ANY^.has_index(heap, current, i) } (pre.fun.V_ARRAY^ANY^.has_index(heap, current, i)) ==> ((fun.V_ARRAY^ANY^.has_index(heap, current, i)) == (((heap[current, V_ARRAY^ANY^.lower_]) <= (i)) && ((i) <= (fun.V_ARRAY^ANY^.upper_(heap, current)))))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun.V_ARRAY^ANY^.has_index(h, current, i), fun.V_ARRAY^ANY^.has_index(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^ANY^.has_index(h, current, i)) && (pre.fun.V_ARRAY^ANY^.has_index(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY^ANY^.has_index(h, current, i)))) ==> ((fun.V_ARRAY^ANY^.has_index(h, current, i)) == (fun.V_ARRAY^ANY^.has_index(h', current, i)))));

function modify.V_ARRAY^ANY^.item(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T48> $o: ref, $f: Field T48 :: { modify.V_ARRAY^ANY^.item(heap, current, i)[$o, $f] } (modify.V_ARRAY^ANY^.item(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^ANY^.item(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T49> $o: ref, $f: Field T49 :: { read.fun.V_ARRAY^ANY^.item(heap, current, i)[$o, $f] } (read.fun.V_ARRAY^ANY^.item(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^ANY^.item(heap: HeapType, current: ref, i: int) returns (bool) {
  (fun.V_ARRAY^ANY^.has_index(heap, current, i)) && (is_closed(heap, current))
}

function trigger.fun.V_ARRAY^ANY^.item(heap: HeapType, current: ref, i: int) returns (bool);

function modify.V_ARRAY2^ANY^.upper_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T50> $o: ref, $f: Field T50 :: { modify.V_ARRAY2^ANY^.upper_(heap, current)[$o, $f] } (modify.V_ARRAY2^ANY^.upper_(heap, current)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.upper_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T51> $o: ref, $f: Field T51 :: { read.fun.V_ARRAY2^ANY^.upper_(heap, current)[$o, $f] } (read.fun.V_ARRAY2^ANY^.upper_(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.upper_(heap: HeapType, current: ref) returns (bool) {
  true
}

function trigger.fun.V_ARRAY2^ANY^.upper_(heap: HeapType, current: ref) returns (bool);

const unique V_SEQUENCE_ITERATOR^ANY^: Type;

axiom ((V_SEQUENCE_ITERATOR^ANY^) <: (V_ITERATOR^ANY^));

axiom ((forall t: Type :: { (V_SEQUENCE_ITERATOR^ANY^) <: (t) } ((V_SEQUENCE_ITERATOR^ANY^) <: (t)) <==> (((t) == (V_SEQUENCE_ITERATOR^ANY^)) || ((V_ITERATOR^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_SEQUENCE_ITERATOR^ANY^)) == (-1));

axiom ((FieldId(closed, V_SEQUENCE_ITERATOR^ANY^)) == (-2));

axiom ((FieldId(owner, V_SEQUENCE_ITERATOR^ANY^)) == (-3));

axiom ((FieldId(owns, V_SEQUENCE_ITERATOR^ANY^)) == (-4));

axiom ((FieldId(observers, V_SEQUENCE_ITERATOR^ANY^)) == (-5));

axiom ((FieldId(subjects, V_SEQUENCE_ITERATOR^ANY^)) == (-6));

const unique V_IO_ITERATOR^ANY^: Type;

axiom ((V_IO_ITERATOR^ANY^) <: (V_ITERATOR^ANY^));

axiom ((V_IO_ITERATOR^ANY^) <: (V_OUTPUT_STREAM^ANY^));

axiom ((forall t: Type :: { (V_IO_ITERATOR^ANY^) <: (t) } ((V_IO_ITERATOR^ANY^) <: (t)) <==> (((t) == (V_IO_ITERATOR^ANY^)) || ((V_ITERATOR^ANY^) <: (t)) || ((V_OUTPUT_STREAM^ANY^) <: (t)))));

axiom ((FieldId(allocated, V_IO_ITERATOR^ANY^)) == (-1));

axiom ((FieldId(closed, V_IO_ITERATOR^ANY^)) == (-2));

axiom ((FieldId(owner, V_IO_ITERATOR^ANY^)) == (-3));

axiom ((FieldId(owns, V_IO_ITERATOR^ANY^)) == (-4));

axiom ((FieldId(observers, V_IO_ITERATOR^ANY^)) == (-5));

axiom ((FieldId(subjects, V_IO_ITERATOR^ANY^)) == (-6));

axiom ((forall <T52> $f: Field T52 :: { IsModelField($f, V_MUTABLE_SEQUENCE^ANY^) } (IsModelField($f, V_MUTABLE_SEQUENCE^ANY^)) <==> ((($f) == (V_MUTABLE_SEQUENCE^ANY^.sequence)) || (($f) == (V_MUTABLE_SEQUENCE^ANY^.lower_)) || (($f) == (V_MUTABLE_SEQUENCE^ANY^.bag)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_MUTABLE_SEQUENCE^ANY^.user_inv(heap: HeapType, current: ref) returns (bool) {
  (!(heap[current, observers][current])) && ((Seq#IsEmpty(heap[current, V_MUTABLE_SEQUENCE^ANY^.sequence])) ==> ((heap[current, V_MUTABLE_SEQUENCE^ANY^.lower_]) == (1))) && (Bag#Equal(heap[current, V_MUTABLE_SEQUENCE^ANY^.bag], Seq#ToBag(heap[current, V_MUTABLE_SEQUENCE^ANY^.sequence]))) && (admissibility2(heap, current))
}

function V_MUTABLE_SEQUENCE^ANY^.V_MUTABLE_SEQUENCE^ANY^.bag.static(heap: HeapType, current: ref) returns (Bag (ref)) {
  Seq#ToBag(heap[current, V_MUTABLE_SEQUENCE^ANY^.sequence])
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((user_inv(heap, current)) <==> (V_MUTABLE_SEQUENCE^ANY^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((user_inv(heap, current)) ==> (V_MUTABLE_SEQUENCE^ANY^.user_inv(heap, current)))));

function modify.V_ARRAY_ITERATOR^ANY^.make(heap: HeapType, current: ref, t: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, t: ref, i: int :: (IsHeap(heap)) ==> ((forall <T53> $o: ref, $f: Field T53 :: { modify.V_ARRAY_ITERATOR^ANY^.make(heap, current, t, i)[$o, $f] } (modify.V_ARRAY_ITERATOR^ANY^.make(heap, current, t, i)[$o, $f]) <==> (((($o) == (t)) && ((($f) == (observers)) || (($f) == (closed)))) || (($o) == (current)))))));

function modify.V_ARRAY2^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T54> $o: ref, $f: Field T54 :: { modify.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current)[$o, $f] } (modify.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T55> $o: ref, $f: Field T55 :: { read.fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current)[$o, $f] } (read.fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap, current)[$o, $f]) <==> (universe[$o])))));

function pre.fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (bool) {
  true
}

function trigger.fun.V_ARRAY2^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (bool);

procedure V_ARRAY^ANY^.is_closed_with_subjects(Current: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.is_closed_with_subjects(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.is_closed_with_subjects(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^ANY^.is_closed_with_subjects(Heap, Current), readable);



function fun.V_ARRAY^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (bool);

function fun0.V_ARRAY^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, current) } { trigger.fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, current) } (pre.fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, current)) ==> ((fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, current)) == ((is_closed(heap, current)) && ((forall i_22: ref :: (heap[current, subjects][i_22]) ==> (is_closed(heap, i_22))))))));

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, current) } (fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, current)) == (fun0.V_ARRAY^ANY^.is_closed_with_subjects(heap, current))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun0.V_ARRAY^ANY^.is_closed_with_subjects(h, current), fun0.V_ARRAY^ANY^.is_closed_with_subjects(h', current) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^ANY^.is_closed_with_subjects(h, current)) && (pre.fun.V_ARRAY^ANY^.is_closed_with_subjects(h', current)) && (same_inside(h, h', read.fun.V_ARRAY^ANY^.is_closed_with_subjects(h, current)))) ==> ((fun0.V_ARRAY^ANY^.is_closed_with_subjects(h, current)) == (fun0.V_ARRAY^ANY^.is_closed_with_subjects(h', current)))));

procedure V_ARRAY^ANY^.is_model_equal(Current: ref, other: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires attached_exact(Heap, other, V_ARRAY^ANY^); // info:type property for argument other
  modifies Heap;
  requires (other) != (Void); // type:pre tag:other /= Void line:731
  ensures ((other) == (Current)) ==> (Result); // type:post tag:reflexive line:737
  ensures (other) != (Void); // type:attached tag:symmetric line:738
  ensures pre.fun.V_ARRAY^ANY^.is_model_equal(Heap, other, Current); // type:check tag:function_precondition line:738 cid:63 rid:79
  ensures (Result) == (fun.V_ARRAY^ANY^.is_model_equal(Heap, other, Current)); // type:post tag:symmetric line:738
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.is_model_equal(Heap, Current, other), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.is_model_equal(old(Heap), Current, other));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^ANY^.is_model_equal(Heap, Current, other), readable);



function fun.V_ARRAY^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

function fun0.V_ARRAY^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.V_ARRAY^ANY^.is_model_equal(heap, current, other) } (pre.fun.V_ARRAY^ANY^.is_model_equal(heap, current, other)) ==> ((((other) == (current)) ==> (fun.V_ARRAY^ANY^.is_model_equal(heap, current, other))) && ((fun.V_ARRAY^ANY^.is_model_equal(heap, current, other)) == (fun.V_ARRAY^ANY^.is_model_equal(heap, other, current))))));

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.V_ARRAY^ANY^.is_model_equal(heap, current, other) } { trigger.fun.V_ARRAY^ANY^.is_model_equal(heap, current, other) } (pre.fun.V_ARRAY^ANY^.is_model_equal(heap, current, other)) ==> ((fun.V_ARRAY^ANY^.is_model_equal(heap, current, other)) == ((Seq#Equal(heap[current, V_ARRAY^ANY^.sequence], heap[other, V_ARRAY^ANY^.sequence])) && ((heap[current, V_ARRAY^ANY^.lower_]) == (heap[other, V_ARRAY^ANY^.lower_]))))));

axiom ((forall heap: HeapType, current: ref, other: ref :: { fun.V_ARRAY^ANY^.is_model_equal(heap, current, other) } (fun.V_ARRAY^ANY^.is_model_equal(heap, current, other)) == (fun0.V_ARRAY^ANY^.is_model_equal(heap, current, other))));

axiom ((forall h: HeapType, h': HeapType, current: ref, other: ref :: { HeapSucc(h, h'), fun0.V_ARRAY^ANY^.is_model_equal(h, current, other), fun0.V_ARRAY^ANY^.is_model_equal(h', current, other) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^ANY^.is_model_equal(h, current, other)) && (pre.fun.V_ARRAY^ANY^.is_model_equal(h', current, other)) && (same_inside(h, h', read.fun.V_ARRAY^ANY^.is_model_equal(h, current, other)))) ==> ((fun0.V_ARRAY^ANY^.is_model_equal(h, current, other)) == (fun0.V_ARRAY^ANY^.is_model_equal(h', current, other)))));

function modify.V_ARRAY^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T56> $o: ref, $f: Field T56 :: { modify.V_ARRAY^ANY^.is_equal_(heap, current, other)[$o, $f] } (modify.V_ARRAY^ANY^.is_equal_(heap, current, other)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T57> $o: ref, $f: Field T57 :: { read.fun.V_ARRAY^ANY^.is_equal_(heap, current, other)[$o, $f] } (read.fun.V_ARRAY^ANY^.is_equal_(heap, current, other)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (bool) {
  (fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, current)) && (fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, other)) && (is_closed(heap, current)) && (is_closed(heap, other))
}

function trigger.fun.V_ARRAY^ANY^.is_equal_(heap: HeapType, current: ref, other: ref) returns (bool);

function pre.fun.MML_SEQUENCE^ANY^.replaced_at(current: Seq (ref), i: int, x: ref) returns (bool) {
  Seq#Domain(current)[i]
}

function trigger.fun.MML_SEQUENCE^ANY^.replaced_at(current: Seq (ref), i: int, x: ref) returns (bool);

function modify.V_ARRAY2^ANY^.idx(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T58> $o: ref, $f: Field T58 :: { modify.V_ARRAY2^ANY^.idx(heap, current, i)[$o, $f] } (modify.V_ARRAY2^ANY^.idx(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.idx(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T59> $o: ref, $f: Field T59 :: { read.fun.V_ARRAY2^ANY^.idx(heap, current, i)[$o, $f] } (read.fun.V_ARRAY2^ANY^.idx(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.idx(heap: HeapType, current: ref, i: int) returns (bool) {
  true
}

function trigger.fun.V_ARRAY2^ANY^.idx(heap: HeapType, current: ref, i: int) returns (bool);

procedure V_ARRAY^ANY^.idx(Current: ref, i: int) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires is_integer_32(i); // info:type property for argument i
  modifies Heap;
  ensures (Result) == (((i) - (Heap[Current, V_ARRAY^ANY^.lower_])) + (1)); // type:post tag:Result = i - lower_ + 1 line:232
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.idx(Heap, Current, i), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.idx(old(Heap), Current, i));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^ANY^.idx(Heap, Current, i), readable);



function fun.V_ARRAY^ANY^.idx(heap: HeapType, current: ref, i: int) returns (int);

function fun0.V_ARRAY^ANY^.idx(heap: HeapType, current: ref, i: int) returns (int);

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^ANY^.idx(heap, current, i) } (pre.fun.V_ARRAY^ANY^.idx(heap, current, i)) ==> (((fun.V_ARRAY^ANY^.idx(heap, current, i)) == (((i) - (heap[current, V_ARRAY^ANY^.lower_])) + (1))) && (is_integer_32(fun.V_ARRAY^ANY^.idx(heap, current, i))))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^ANY^.idx(heap, current, i) } { trigger.fun.V_ARRAY^ANY^.idx(heap, current, i) } (pre.fun.V_ARRAY^ANY^.idx(heap, current, i)) ==> ((fun.V_ARRAY^ANY^.idx(heap, current, i)) == (((i) - (heap[current, V_ARRAY^ANY^.lower_])) + (1)))));

axiom ((forall heap: HeapType, current: ref, i: int :: { fun.V_ARRAY^ANY^.idx(heap, current, i) } (fun.V_ARRAY^ANY^.idx(heap, current, i)) == (fun0.V_ARRAY^ANY^.idx(heap, current, i))));

axiom ((forall h: HeapType, h': HeapType, current: ref, i: int :: { HeapSucc(h, h'), fun0.V_ARRAY^ANY^.idx(h, current, i), fun0.V_ARRAY^ANY^.idx(h', current, i) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^ANY^.idx(h, current, i)) && (pre.fun.V_ARRAY^ANY^.idx(h', current, i)) && (same_inside(h, h', read.fun.V_ARRAY^ANY^.idx(h, current, i)))) ==> ((fun0.V_ARRAY^ANY^.idx(h, current, i)) == (fun0.V_ARRAY^ANY^.idx(h', current, i)))));

function modify.V_ARRAY^ANY^.put(heap: HeapType, current: ref, v: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, v: ref, i: int :: (IsHeap(heap)) ==> ((forall <T60> $o: ref, $f: Field T60 :: { modify.V_ARRAY^ANY^.put(heap, current, v, i)[$o, $f] } (modify.V_ARRAY^ANY^.put(heap, current, v, i)[$o, $f]) <==> ((($o) == (current)) && ((!(IsModelField($f, V_ARRAY^ANY^))) || (($f) == (V_ARRAY^ANY^.sequence)) || (($f) == (V_ARRAY^ANY^.bag))))))));

const unique ITERABLE^ANY^: Type;

axiom ((ITERABLE^ANY^) <: (ANY));

axiom ((forall t: Type :: { (ITERABLE^ANY^) <: (t) } ((ITERABLE^ANY^) <: (t)) <==> (((t) == (ITERABLE^ANY^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, ITERABLE^ANY^)) == (-1));

axiom ((FieldId(closed, ITERABLE^ANY^)) == (-2));

axiom ((FieldId(owner, ITERABLE^ANY^)) == (-3));

axiom ((FieldId(owns, ITERABLE^ANY^)) == (-4));

axiom ((FieldId(observers, ITERABLE^ANY^)) == (-5));

axiom ((FieldId(subjects, ITERABLE^ANY^)) == (-6));

function modify.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T61> $o: ref, $f: Field T61 :: { modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T62> $o: ref, $f: Field T62 :: { read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.ANY.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.ANY.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.V_ARRAY2^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T63> $o: ref, $f: Field T63 :: { modify.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY2^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T64> $o: ref, $f: Field T64 :: { read.fun.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_ARRAY2^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY2^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_ARRAY2^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function pre.fun.MML_SET^ANY^.default_create() returns (bool) {
  true
}

function trigger.fun.MML_SET^ANY^.default_create() returns (bool);

procedure V_ITERATOR^ANY^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ITERATOR^ANY^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ITERATOR^ANY^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ITERATOR^ANY^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ITERATOR^ANY^.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o) } { trigger.fun.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o) } (pre.fun.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)) ==> ((fun.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)) == ((attached(heap, o, ANY)) && (new_observers[o])))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o) } (fun.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)) == (fun0.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_ITERATOR^ANY^.in_observers(h, current, new_observers, o), fun0.V_ITERATOR^ANY^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_ITERATOR^ANY^.in_observers(h, current, new_observers, o)) && (pre.fun.V_ITERATOR^ANY^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_ITERATOR^ANY^.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_ITERATOR^ANY^.in_observers(h, current, new_observers, o)) == (fun0.V_ITERATOR^ANY^.in_observers(h', current, new_observers, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_CONTAINER^ANY^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_CONTAINER^ANY^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_CONTAINER^ANY^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_CONTAINER^ANY^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_CONTAINER^ANY^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_CONTAINER^ANY^.in_observers(heap, current, v, o)))));

const unique V_OUTPUT_STREAM^ANY^: Type;

axiom ((V_OUTPUT_STREAM^ANY^) <: (ANY));

axiom ((forall t: Type :: { (V_OUTPUT_STREAM^ANY^) <: (t) } ((V_OUTPUT_STREAM^ANY^) <: (t)) <==> (((t) == (V_OUTPUT_STREAM^ANY^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, V_OUTPUT_STREAM^ANY^)) == (-1));

axiom ((FieldId(closed, V_OUTPUT_STREAM^ANY^)) == (-2));

axiom ((FieldId(owner, V_OUTPUT_STREAM^ANY^)) == (-3));

axiom ((FieldId(owns, V_OUTPUT_STREAM^ANY^)) == (-4));

axiom ((FieldId(observers, V_OUTPUT_STREAM^ANY^)) == (-5));

axiom ((FieldId(subjects, V_OUTPUT_STREAM^ANY^)) == (-6));

procedure V_ARRAY_ITERATOR^ANY^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY_ITERATOR^ANY^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY_ITERATOR^ANY^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY_ITERATOR^ANY^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY_ITERATOR^ANY^.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_ARRAY_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o) } { trigger.fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o) } (pre.fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)) ==> ((fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)) == ((attached(heap, o, ANY)) && (new_observers[o])))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o) } (fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)) == (fun0.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_ARRAY_ITERATOR^ANY^.in_observers(h, current, new_observers, o), fun0.V_ARRAY_ITERATOR^ANY^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY_ITERATOR^ANY^.in_observers(h, current, new_observers, o)) && (pre.fun.V_ARRAY_ITERATOR^ANY^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_ARRAY_ITERATOR^ANY^.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_ARRAY_ITERATOR^ANY^.in_observers(h, current, new_observers, o)) == (fun0.V_ARRAY_ITERATOR^ANY^.in_observers(h', current, new_observers, o)))));

const unique V_SPECIAL^ANY^: Type;

axiom ((V_SPECIAL^ANY^) <: (ANY));

axiom ((forall t: Type :: { (V_SPECIAL^ANY^) <: (t) } ((V_SPECIAL^ANY^) <: (t)) <==> (((t) == (V_SPECIAL^ANY^)) || ((ANY) <: (t)))));

axiom ((FieldId(allocated, V_SPECIAL^ANY^)) == (-1));

axiom ((FieldId(closed, V_SPECIAL^ANY^)) == (-2));

axiom ((FieldId(owner, V_SPECIAL^ANY^)) == (-3));

axiom ((FieldId(owns, V_SPECIAL^ANY^)) == (-4));

axiom ((FieldId(observers, V_SPECIAL^ANY^)) == (-5));

axiom ((FieldId(subjects, V_SPECIAL^ANY^)) == (-6));

axiom ((forall <T65> $f: Field T65 :: { IsModelField($f, V_SPECIAL^ANY^) } (IsModelField($f, V_SPECIAL^ANY^)) <==> ((($f) == (V_SPECIAL^ANY^.sequence)) || (($f) == (V_SPECIAL^ANY^.capacity)) || (($f) == (subjects)) || (($f) == (observers)))));

function { :inline } V_SPECIAL^ANY^.user_inv(heap: HeapType, current: ref) returns (bool) {
  ((Seq#Length(heap[current, V_SPECIAL^ANY^.sequence])) <= (heap[current, V_SPECIAL^ANY^.capacity])) && (Set#IsEmpty(heap[current, observers])) && (Set#IsEmpty(heap[current, subjects])) && (Set#IsEmpty(heap[current, owns])) && (admissibility2(heap, current))
}

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached_exact(heap, current, V_SPECIAL^ANY^)) ==> ((user_inv(heap, current)) <==> (V_SPECIAL^ANY^.user_inv(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { user_inv(heap, current) } (attached(heap, current, V_SPECIAL^ANY^)) ==> ((user_inv(heap, current)) ==> (V_SPECIAL^ANY^.user_inv(heap, current)))));

procedure V_ARRAY^ANY^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^ANY^.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_ARRAY^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_ARRAY^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o) } { trigger.fun.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o) } (pre.fun.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o)) ==> ((fun.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o)) == ((attached(heap, o, ANY)) && (new_observers[o])))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o) } (fun.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o)) == (fun0.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_ARRAY^ANY^.in_observers(h, current, new_observers, o), fun0.V_ARRAY^ANY^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^ANY^.in_observers(h, current, new_observers, o)) && (pre.fun.V_ARRAY^ANY^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_ARRAY^ANY^.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_ARRAY^ANY^.in_observers(h, current, new_observers, o)) == (fun0.V_ARRAY^ANY^.in_observers(h', current, new_observers, o)))));

procedure V_ARRAY^ANY^.upper_(Current: ref) returns (Result: int where is_integer_32(Result));
  free requires attached_exact(Heap, Current, V_ARRAY^ANY^); // info:type property for argument Current
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_ARRAY^ANY^.upper_(Heap, Current), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_ARRAY^ANY^.upper_(old(Heap), Current));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_ARRAY^ANY^.upper_(Heap, Current), readable);



function fun.V_ARRAY^ANY^.upper_(heap: HeapType, current: ref) returns (int);

function fun0.V_ARRAY^ANY^.upper_(heap: HeapType, current: ref) returns (int);

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY^ANY^.upper_(heap, current) } (pre.fun.V_ARRAY^ANY^.upper_(heap, current)) ==> (is_integer_32(fun.V_ARRAY^ANY^.upper_(heap, current)))));

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY^ANY^.upper_(heap, current) } { trigger.fun.V_ARRAY^ANY^.upper_(heap, current) } (pre.fun.V_ARRAY^ANY^.upper_(heap, current)) ==> ((fun.V_ARRAY^ANY^.upper_(heap, current)) == (((heap[current, V_ARRAY^ANY^.lower_]) + (Seq#Length(heap[current, V_ARRAY^ANY^.sequence]))) - (1)))));

axiom ((forall heap: HeapType, current: ref :: { fun.V_ARRAY^ANY^.upper_(heap, current) } (fun.V_ARRAY^ANY^.upper_(heap, current)) == (fun0.V_ARRAY^ANY^.upper_(heap, current))));

axiom ((forall h: HeapType, h': HeapType, current: ref :: { HeapSucc(h, h'), fun0.V_ARRAY^ANY^.upper_(h, current), fun0.V_ARRAY^ANY^.upper_(h', current) } ((HeapSucc(h, h')) && (pre.fun.V_ARRAY^ANY^.upper_(h, current)) && (pre.fun.V_ARRAY^ANY^.upper_(h', current)) && (same_inside(h, h', read.fun.V_ARRAY^ANY^.upper_(h, current)))) ==> ((fun0.V_ARRAY^ANY^.upper_(h, current)) == (fun0.V_ARRAY^ANY^.upper_(h', current)))));

function modify.V_ARRAY^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T66> $o: ref, $f: Field T66 :: { modify.V_ARRAY^ANY^.has_index(heap, current, i)[$o, $f] } (modify.V_ARRAY^ANY^.has_index(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T67> $o: ref, $f: Field T67 :: { read.fun.V_ARRAY^ANY^.has_index(heap, current, i)[$o, $f] } (read.fun.V_ARRAY^ANY^.has_index(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (bool) {
  is_closed(heap, current)
}

function trigger.fun.V_ARRAY^ANY^.has_index(heap: HeapType, current: ref, i: int) returns (bool);

axiom ((FieldId(V_MUTABLE_SEQUENCE^ANY^.lower_, V_MUTABLE_SEQUENCE^ANY^)) == (93));

axiom ((V_MUTABLE_SEQUENCE^ANY^.lower_) == (V_SEQUENCE^ANY^.lower_));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_MUTABLE_SEQUENCE^ANY^.lower_] } ((IsHeap(heap)) && (attached(heap, o, V_MUTABLE_SEQUENCE^ANY^))) ==> (is_integer_32(heap[o, V_MUTABLE_SEQUENCE^ANY^.lower_]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.lower_, v, o) } (attached_exact(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.lower_, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.lower_, v, o) } (attached(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, V_MUTABLE_SEQUENCE^ANY^.lower_, v, o)) ==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_MUTABLE_SEQUENCE^ANY^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, v, o)))));

function modify.V_ARRAY^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T68> $o: ref, $f: Field T68 :: { modify.V_ARRAY^ANY^.is_closed_with_subjects(heap, current)[$o, $f] } (modify.V_ARRAY^ANY^.is_closed_with_subjects(heap, current)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T69> $o: ref, $f: Field T69 :: { read.fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, current)[$o, $f] } (read.fun.V_ARRAY^ANY^.is_closed_with_subjects(heap, current)[$o, $f]) <==> (universe[$o])))));

function pre.fun.V_ARRAY^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (bool) {
  true
}

function trigger.fun.V_ARRAY^ANY^.is_closed_with_subjects(heap: HeapType, current: ref) returns (bool);

function modify.V_ARRAY^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T70> $o: ref, $f: Field T70 :: { modify.V_ARRAY^ANY^.is_model_equal(heap, current, other)[$o, $f] } (modify.V_ARRAY^ANY^.is_model_equal(heap, current, other)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, other: ref :: (IsHeap(heap)) ==> ((forall <T71> $o: ref, $f: Field T71 :: { read.fun.V_ARRAY^ANY^.is_model_equal(heap, current, other)[$o, $f] } (read.fun.V_ARRAY^ANY^.is_model_equal(heap, current, other)[$o, $f]) <==> (((($o) == (current)) || (($o) == (other))) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool) {
  (other) != (Void)
}

function trigger.fun.V_ARRAY^ANY^.is_model_equal(heap: HeapType, current: ref, other: ref) returns (bool);

function modify.V_ARRAY^ANY^.idx(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T72> $o: ref, $f: Field T72 :: { modify.V_ARRAY^ANY^.idx(heap, current, i)[$o, $f] } (modify.V_ARRAY^ANY^.idx(heap, current, i)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^ANY^.idx(heap: HeapType, current: ref, i: int) returns (Frame);

axiom ((forall heap: HeapType, current: ref, i: int :: (IsHeap(heap)) ==> ((forall <T73> $o: ref, $f: Field T73 :: { read.fun.V_ARRAY^ANY^.idx(heap, current, i)[$o, $f] } (read.fun.V_ARRAY^ANY^.idx(heap, current, i)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^ANY^.idx(heap: HeapType, current: ref, i: int) returns (bool) {
  true
}

function trigger.fun.V_ARRAY^ANY^.idx(heap: HeapType, current: ref, i: int) returns (bool);

function modify.V_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T74> $o: ref, $f: Field T74 :: { modify.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T75> $o: ref, $f: Field T75 :: { read.fun.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

procedure V_CONTAINER^ANY^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_CONTAINER^ANY^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_CONTAINER^ANY^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_CONTAINER^ANY^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_CONTAINER^ANY^.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_CONTAINER^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_CONTAINER^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o) } { trigger.fun.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o) } (pre.fun.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o)) ==> ((fun.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o)) == ((attached(heap, o, ANY)) && (new_observers[o])))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o) } (fun.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o)) == (fun0.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_CONTAINER^ANY^.in_observers(h, current, new_observers, o), fun0.V_CONTAINER^ANY^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_CONTAINER^ANY^.in_observers(h, current, new_observers, o)) && (pre.fun.V_CONTAINER^ANY^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_CONTAINER^ANY^.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_CONTAINER^ANY^.in_observers(h, current, new_observers, o)) == (fun0.V_CONTAINER^ANY^.in_observers(h', current, new_observers, o)))));

function modify.V_ARRAY_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T76> $o: ref, $f: Field T76 :: { modify.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T77> $o: ref, $f: Field T77 :: { read.fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_ARRAY_ITERATOR^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

const V_SPECIAL^ANY^.capacity: Field int;

axiom ((FieldId(V_SPECIAL^ANY^.capacity, V_SPECIAL^ANY^)) == (82));

axiom ((forall heap: HeapType, o: ref :: { heap[o, V_SPECIAL^ANY^.capacity] } ((IsHeap(heap)) && (attached(heap, o, V_SPECIAL^ANY^))) ==> (is_integer_32(heap[o, V_SPECIAL^ANY^.capacity]))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_SPECIAL^ANY^.capacity, v, o) } (attached_exact(heap, current, V_SPECIAL^ANY^)) ==> ((guard(heap, current, V_SPECIAL^ANY^.capacity, v, o)) <==> (false))));

axiom ((forall heap: HeapType, current: ref, v: int, o: ref :: { guard(heap, current, V_SPECIAL^ANY^.capacity, v, o) } (attached(heap, current, V_SPECIAL^ANY^)) ==> ((guard(heap, current, V_SPECIAL^ANY^.capacity, v, o)) ==> (false))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, owns, v, o) } (attached_exact(heap, current, V_SPECIAL^ANY^)) ==> ((guard(heap, current, owns, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, subjects, v, o) } (attached_exact(heap, current, V_SPECIAL^ANY^)) ==> ((guard(heap, current, subjects, v, o)) <==> (true))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached_exact(heap, current, V_SPECIAL^ANY^)) ==> ((guard(heap, current, observers, v, o)) <==> (fun.V_SPECIAL^ANY^.in_observers(heap, current, v, o)))));

axiom ((forall heap: HeapType, current: ref, v: Set (ref), o: ref :: { guard(heap, current, observers, v, o) } (attached(heap, current, V_SPECIAL^ANY^)) ==> ((guard(heap, current, observers, v, o)) ==> (fun.V_SPECIAL^ANY^.in_observers(heap, current, v, o)))));

function modify.V_ARRAY^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T78> $o: ref, $f: Field T78 :: { modify.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T79> $o: ref, $f: Field T79 :: { read.fun.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_ARRAY^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_ARRAY^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.V_ARRAY^ANY^.upper_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T80> $o: ref, $f: Field T80 :: { modify.V_ARRAY^ANY^.upper_(heap, current)[$o, $f] } (modify.V_ARRAY^ANY^.upper_(heap, current)[$o, $f]) <==> (false)))));

function read.fun.V_ARRAY^ANY^.upper_(heap: HeapType, current: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref :: (IsHeap(heap)) ==> ((forall <T81> $o: ref, $f: Field T81 :: { read.fun.V_ARRAY^ANY^.upper_(heap, current)[$o, $f] } (read.fun.V_ARRAY^ANY^.upper_(heap, current)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_ARRAY^ANY^.upper_(heap: HeapType, current: ref) returns (bool) {
  true
}

function trigger.fun.V_ARRAY^ANY^.upper_(heap: HeapType, current: ref) returns (bool);

procedure V_MUTABLE_SEQUENCE^ANY^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_MUTABLE_SEQUENCE^ANY^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_MUTABLE_SEQUENCE^ANY^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_MUTABLE_SEQUENCE^ANY^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o) } { trigger.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o) } (pre.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o)) ==> ((fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o)) == ((attached(heap, o, ANY)) && (new_observers[o])))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o) } (fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o)) == (fun0.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_MUTABLE_SEQUENCE^ANY^.in_observers(h, current, new_observers, o), fun0.V_MUTABLE_SEQUENCE^ANY^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(h, current, new_observers, o)) && (pre.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_MUTABLE_SEQUENCE^ANY^.in_observers(h, current, new_observers, o)) == (fun0.V_MUTABLE_SEQUENCE^ANY^.in_observers(h', current, new_observers, o)))));

function modify.V_CONTAINER^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T82> $o: ref, $f: Field T82 :: { modify.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_CONTAINER^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T83> $o: ref, $f: Field T83 :: { read.fun.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_CONTAINER^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_CONTAINER^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_CONTAINER^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

procedure V_SPECIAL^ANY^.in_observers(Current: ref, new_observers: Set (ref), o: ref) returns (Result: bool where true);
  free requires attached_exact(Heap, Current, V_SPECIAL^ANY^); // info:type property for argument Current
  free requires Set#ItemsType(Heap, new_observers, ANY); // info:type property for argument new_observers
  free requires Heap[o, allocated]; // info:type property for argument o
  modifies Heap;
  free requires global(Heap);
  free ensures global(Heap);
  requires Frame#Subset(modify.V_SPECIAL^ANY^.in_observers(Heap, Current, new_observers, o), writable); // type:pre tag:frame_writable
  free requires closed_under_domains(writable, Heap);
  free ensures same_outside(old(Heap), Heap, modify.V_SPECIAL^ANY^.in_observers(old(Heap), Current, new_observers, o));
  free ensures HeapSucc(old(Heap), Heap);
  free requires Frame#Subset(read.fun.V_SPECIAL^ANY^.in_observers(Heap, Current, new_observers, o), readable);



function fun.V_SPECIAL^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function fun0.V_SPECIAL^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o) } { trigger.fun.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o) } (pre.fun.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o)) ==> ((fun.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o)) == ((attached(heap, o, ANY)) && (new_observers[o])))));

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: { fun.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o) } (fun.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o)) == (fun0.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o))));

axiom ((forall h: HeapType, h': HeapType, current: ref, new_observers: Set (ref), o: ref :: { HeapSucc(h, h'), fun0.V_SPECIAL^ANY^.in_observers(h, current, new_observers, o), fun0.V_SPECIAL^ANY^.in_observers(h', current, new_observers, o) } ((HeapSucc(h, h')) && (pre.fun.V_SPECIAL^ANY^.in_observers(h, current, new_observers, o)) && (pre.fun.V_SPECIAL^ANY^.in_observers(h', current, new_observers, o)) && (same_inside(h, h', read.fun.V_SPECIAL^ANY^.in_observers(h, current, new_observers, o)))) ==> ((fun0.V_SPECIAL^ANY^.in_observers(h, current, new_observers, o)) == (fun0.V_SPECIAL^ANY^.in_observers(h', current, new_observers, o)))));

function modify.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T84> $o: ref, $f: Field T84 :: { modify.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T85> $o: ref, $f: Field T85 :: { read.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_MUTABLE_SEQUENCE^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);

function modify.V_SPECIAL^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T86> $o: ref, $f: Field T86 :: { modify.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (modify.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> (false)))));

function read.fun.V_SPECIAL^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (Frame);

axiom ((forall heap: HeapType, current: ref, new_observers: Set (ref), o: ref :: (IsHeap(heap)) ==> ((forall <T87> $o: ref, $f: Field T87 :: { read.fun.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o)[$o, $f] } (read.fun.V_SPECIAL^ANY^.in_observers(heap, current, new_observers, o)[$o, $f]) <==> ((universe[$o]) && (($f) != (closed)) && (($f) != (owner)))))));

function pre.fun.V_SPECIAL^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool) {
  true
}

function trigger.fun.V_SPECIAL^ANY^.in_observers(heap: HeapType, current: ref, new_observers: Set (ref), o: ref) returns (bool);


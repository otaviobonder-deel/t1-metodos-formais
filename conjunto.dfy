class Conjunto {
    ghost var conjunto: set<nat>;

    var lista: array<int>;
    var n: nat;

    predicate ConjuntoValido()
    reads this, lista;
    {
        n <= lista.Length
        && (forall x:int :: x in conjunto <==> exists j:nat :: j<n && lista[j] == x)
        && (forall i:nat, j:nat :: i<j<n ==> lista[i] != lista[j])
    }

    constructor ()
    ensures conjunto == {};
    ensures ConjuntoValido();
    ensures fresh(lista);
    {
        lista := new int[10] ;
        n := 0 ;
        conjunto := {} ;
    }


    method resize()
        requires ConjuntoValido() ;
        ensures ConjuntoValido();
        modifies this;
        ensures conjunto == old(conjunto) && n == old(n);
        ensures lista.Length > old(lista.Length);
        ensures fresh(lista);
        ensures (forall i:nat :: i<n ==> lista[i] == old(lista[i]));
        {
            var anew := new int[2 * lista.Length + 1];
            // copy all elements from a into anew
            var i:nat := 0;
            while (i < n)
                invariant i <= n;
                invariant forall j:nat :: j<i ==> anew[j] == lista[j];
                modifies anew;
                {
                    anew[i] := lista[i];
                    i := i + 1 ;
                }
            
                lista := anew;
        }

    method contains(x:nat) returns (b:bool)
        requires ConjuntoValido();
        ensures ConjuntoValido();
        ensures b <==> x in conjunto;
        {
            var i:nat := 0;
            while (i < n)
                invariant i <= n;
                invariant (forall j:nat :: j<i ==> lista[j] != x);
                {
                    if (lista[i] == x) {
                        return true;
                    }
                    i := i + 1;
                }
            return false;
        }

    method add(x:int)
        requires ConjuntoValido();
        modifies this, lista;
        ensures ConjuntoValido();
        ensures conjunto == old(conjunto) + { x };
        {
            var i:nat := 0;
            while (i < n)
                invariant i <= n;
                invariant forall j:nat :: j<i ==> lista[j] != x;
                invariant ConjuntoValido();
                {
                    if (lista[i] == x) {
                        return;
                    }
                    i := i + 1;
                }
                if (i >= lista.Length) {
                    resize();
                }
	
                lista[i] := x;
                n := n + 1;

                conjunto := conjunto + { x };
        }

}

method Main()
    {
        var conj1 := new Conjunto() ;

        conj1.add(3) ;

        var b := conj1.contains(3) ;
        assert b == true ;
    }
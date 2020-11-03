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
        lista := new int[10];
        n := 0;
        conjunto := {};
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
            decreases n - i
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
            decreases n - i
            invariant i <= n
            invariant (forall j:nat :: j<i ==> lista[j] != x)
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
            decreases n - i
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

    method size() returns (n:int)
        requires ConjuntoValido();
        ensures ConjuntoValido();
        {
            return lista.Length;
        }

    method isEmpty() returns (b:bool)
        requires ConjuntoValido();
        ensures ConjuntoValido();
        {
            if (lista.Length == 0) {
                return true;
            }
            return false;
        }

    method remove(x:int) returns (b:bool)
    requires ConjuntoValido();
    requires lista.Length > 0;
    ensures ConjuntoValido();
    modifies this, lista;
    {
        var c:bool := false;
        var j:nat := 0;
        
        while (j < n)
        invariant 0 <= j <= n
        decreases n - j
            {
            if (lista[j] == x) {
                c := true;
            }
            j := j + 1;
        }

        if (c == false) {
            return false;
        }

        var anew := new int[lista.Length - 1];
        var i:nat := 0;
        while (i < lista.Length && lista[i] != x)
        decreases lista.Length - i
        invariant 0 <= i < lista.Length
        {
            anew[i] := lista[i];
            i := i + 1;
        }

        while (i < n)
        decreases n - i
        invariant 0 <= i <= lista.Length
        invariant anew.Length < lista.Length
        {
            anew[i - 1] := lista[i];
            i := i + 1;
        }

        lista := anew;

        return true;

    }


}

method Main()
    {
        var conj1 := new Conjunto() ;

        conj1.add(3) ;

        var b := conj1.contains(3) ;
        assert b == true ;
    }
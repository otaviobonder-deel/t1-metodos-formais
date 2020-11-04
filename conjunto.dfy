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

    method array_contains(a:array<int>, number:int) returns (b:bool)
        {
            var i := 0;
            while(i < a.Length)
            decreases a.Length - i
            invariant 0 <= i <= a.Length
            {
                if(a[i] == number){
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

        c := true;

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

    method array_union(array_1: array<int>, array_2: array<int>) returns (a:array<int>) 
    requires array_1.Length >= 0
    requires array_2.Length >= 0
    {
        var result := new int[array_1.Length + array_2.Length];
        var i:nat := 0;
        while(i < array_1.Length)
        decreases array_1.Length - i
        invariant 0 <= i <= array_1.Length
        {
            result[i] := array_1[i];
            i := i + 1;
        }

        var j:nat := 0;
        while(j < array_2.Length && i < result.Length)
        decreases array_2.Length - j
        invariant 0 <= j <= array_2.Length
        {
            result[i] := array_2[j];
            i := i + 1;
            j := j + 1;
        }

        return result;
    }

    method conjunto_union(conjunto_1: Conjunto, conjunto_2: Conjunto) returns (conjunto_resultado: Conjunto)
    requires conjunto_1.ConjuntoValido()
    requires conjunto_2.ConjuntoValido()
    {
        var result := new Conjunto();

        result.lista := array_union(conjunto_1.lista, conjunto_2.lista);
        result.n := result.lista.Length;

        return result;
    }

    method array_intersection(array_1: array<int>, array_2: array<int>) returns (a:array<int>) 
    requires array_1.Length >= 0
    requires array_2.Length >= 0
    {
        var result := new int[array_1.Length + array_2.Length];
        var r:nat := 0;
        var contains := false;

        var i:nat := 0;
        while(i < array_1.Length && r < result.Length)
        decreases array_1.Length - i
        invariant 0 <= i <= array_1.Length
        {
            contains := array_contains(array_2, array_1[i]);
            if(contains == true) {
                result[r] := array_1[i];
                r := r + 1;
            }
            i := i + 1;
            contains := false;
        }

        var j:nat := 0;
        while(j < array_2.Length && r < result.Length)
        decreases array_2.Length - j
        invariant 0 <= j <= array_2.Length
        {
            contains := array_contains(array_1, array_2[j]);
            if(contains == true) {
                result[r] := array_2[j];
                r := r + 1;
            }
            j := j + 1;
            contains := false;
        }

        var resized_result := new int[r];
        r := 0;
        while(r < resized_result.Length && r < result.Length)
        decreases resized_result.Length - r
        invariant 0 <= r <= resized_result.Length
        {
            resized_result[r] := result[r];
            r := r + 1;
        }

        return resized_result;
    }

    method conjunto_intersection(conjunto_1: Conjunto, conjunto_2: Conjunto) returns (conjunto_resultado: Conjunto)
    requires conjunto_1.ConjuntoValido()
    requires conjunto_2.ConjuntoValido()
    {
        var result := new Conjunto();
        var n:int;

        result.lista := array_intersection(conjunto_1.lista, conjunto_2.lista);
        result.n := result.lista.Length;

        return result;
    }

    method array_difference(array_1: array<int>, array_2: array<int>) returns (a:array<int>) 
    requires array_1.Length >= 0
    requires array_2.Length >= 0
    {
        var result := new int[array_1.Length + array_2.Length];
        var r:nat := 0;
        var contains := true;

        var i:nat := 0;
        while(i < array_1.Length && r < result.Length)
        decreases array_1.Length - i
        invariant 0 <= i <= array_1.Length
        {
            contains := array_contains(array_2, array_1[i]);
            if(contains == false) {
                result[r] := array_1[i];
                r := r + 1;
            }
            i := i + 1;
            contains := true;
        }

        var j:nat := 0;
        while(j < array_2.Length && r < result.Length)
        decreases array_2.Length - j
        invariant 0 <= j <= array_2.Length
        {
            contains := array_contains(array_1, array_2[j]);
            if(contains == false) {
                result[r] := array_2[j];
                r := r + 1;
            }
            j := j + 1;
            contains := true;
        }

        var resized_result := new int[r];
        r := 0;
        while(r < resized_result.Length && r < result.Length)
        decreases resized_result.Length - r
        invariant 0 <= r <= resized_result.Length
        {
            resized_result[r] := result[r];
            r := r + 1;
        }

        return resized_result;
    }

    method conjunto_difference(conjunto_1: Conjunto, conjunto_2: Conjunto) returns (conjunto_resultado: Conjunto)
    requires conjunto_1.ConjuntoValido()
    requires conjunto_2.ConjuntoValido()
    {
        var result := new Conjunto();
        var n:int;

        result.lista := array_difference(conjunto_1.lista, conjunto_2.lista);
        result.n := result.lista.Length;

        return result;
    }


}

method Main()
    {
        var conj1 := new Conjunto() ;

        conj1.add(3) ;

        var b := conj1.contains(3) ;
        assert b == true ;

    }
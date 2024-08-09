// ----------------------- From p-reg-partitions.magma ----------------------------------------

// Functions on partitions

// Partitions: use Magma's built in function Partitions(n)

function isPRegular(parts,p)
    if #parts eq 0 then
        return true;
    end if;
    count := [#[0 : part in parts | part eq n] : n in Set(parts) | n ne 0];
    return Max(count) lt p;
end function;

// Functions on p-regular partitions
function pRegularPartitions(n, p)
    return [partition : partition in Partition(n) | isPRegular(partition,p)];
end function;


function pContent(row,column,p) // indexing both from 0
    return (column - row) mod p;
end function;



function reducedSignature(sig)
    // iterative O(n) way to do "remove -+" recursion
    sigReduced := [];
    minusStack := [];
    for box in sig do
        direction := box[3];
        if direction gt 0 then
            if #minusStack gt 0 then
                Prune(~minusStack);
            else
                Append(~sigReduced, box);
            end if;
        elif direction lt 0 then
            Append(~minusStack, box);
        end if;
    end for;
    return sigReduced cat minusStack;
end function;

// Signature (row,column,direction), where direction is 1=add or -1=remove
// Note: different from python implementation because magma indexes from 1
function iSignature(parts, i, p : reduced := false)
    if not isPRegular(parts,p) then
        Error("Error in iSignature: partition is not p-regular!");
    end if;
    if i ge p then
        Error("Error in iSignature: i must be strictly less than p");
    end if;
    parts := [n : n in Sort(parts) | n ne 0]; // looking at partition from small to big

    c := pContent(#parts+1,1,p);
    iSig := c eq i select [<#parts+1,1,1>] else []; // content of first box in a new row
    for j -> part in parts do
        c := pContent(#parts+1-j,part,p); // content of the last box in row j
        if c eq i and (j eq 1 or parts[j-1] lt part) then
            // and = check if removing makes it a partition
            Append(~iSig,<#parts+1-j,part,-1>);
        elif ((c+1) mod p) eq i and (j eq #parts or parts[j+1] gt part) then
            // and = check if adding makes it a partition
            Append(~iSig, <#parts+1-j,part+1,1>);
        end if;
    end for;
    return (not reduced) select iSig else reducedSignature(iSig);
end function;

function iSocleInductionPartition(parts,i,p)
    if not isPRegular(parts,p) then
        Error("Error in iSocleInductionPartition: partition is not p-regular!");
    end if;
    if i ge p then
        Error("Error in iSocleInductionPartition: i must be strictly less than p");
    end if;
    parts := [n : n in Reverse(Sort(parts)) | n ne 0]; // looking at partition from small to big

    iSig := iSignature(parts,i,p : reduced := true);
    for box in Reverse(iSig) do
        if box[3] gt 0 then
            iAddableBox := box;
            if iAddableBox[1] le #parts then
                // adding to existing row
                parts[iAddableBox[1]] := parts[iAddableBox[1]] + 1;
            else
                // adding new row
                Append(~parts,1);
            end if;
            return parts;
        end if;
    end for;
    // Function should never get here
    Error("Error in iSocleInductionPartition: cannot induce partition with given i,p");
end function;


function iSocleRestrictionPartition(parts,i,p)
    if not isPRegular(parts,p) then
        Error("Error in iSocleRestrictionPartition: partition is not p-regular!");
    end if;
    if i ge p then
        Error("Error in iSocleRestrictionPartition: i must be strictly less than p");
    end if;
    parts := [n : n in Reverse(Sort(parts)) | n ne 0];
    if #parts eq 0 then
        Error("Error in iSocleRestrictionPartition: cannot restrict empty partition");
    end if;

    iSig := iSignature(parts,i,p : reduced := true);
    for box in Reverse(iSig) do
        if box[3] lt 0 then
            iRemovableBox := box;
            // remove from existing row
            parts[iRemovableBox[1]] := parts[iRemovableBox[1]] - 1;
            parts := [x : x in parts | x ne 0]; // vanish the 0s
            return parts;
        end if;
    end for;
    // Function should never get here
    Error("Error in iSocleRestrictionPartition: cannot restrict partition with given i,p");
end function;


// -----------------------------------------------------------------------------------------

JM := function (k, G, r)
   dim := Degree(Codomain(r));
   sum := 0; // knows later it's a zero matrix
   for i := 1 to k-1 do
       sum := sum + r(G!(i,k));
   end for;
   return sum;
end function;

function deltaVector(F, n, i)
    /*
    Parameters: F : Fld
               n : Nat
               i : [1..n]
    Returns the i-th standard basis column vector of F^n
    */

    Q := [0 : k in [1..n]];
    Q[i] := 1;
    return Matrix(F, n, 1, Q);
end function;

//A := Matrix(GF(3), 3, 3, [2, 1, 0, 0, 2, 0, 0, 0, 1]);
function generalisedEigenspace(A, i)
    /*
    Parameters: A : Square matrix over a field k
                i : Element of k
    Return generalised eigenspace of A with respect to eigenvalue i
    */

    groundField := Parent(A[1][1]);
    R, T, F := JordanForm(A);
    n_total := 0;
    idcs := [];

    //Get list of all indices belonging to Jordan blocks with eigenvalue i
    for j := 1 to #F do
        eigval := -ConstantCoefficient(F[j][1]);
        block_size := F[j][2];
        if eigval eq i then
            new_idcs := [k + n_total : k in [1..block_size]];
            idcs := idcs cat new_idcs;
        end if;
        n_total := n_total + block_size;
    end for;

    //n_total is now equal to the number of columns of A.
    //Get basis of generalised eigenvectors
    eigvects := [];
    for j := 1 to #idcs do
        v := Vector(T^-1*deltaVector(groundField, n_total, idcs[j]));
        eigvects := Append(eigvects, v);
    end for;
    //return eigvects;
 
    //Create subspace spanned by generalised eigenvectors
    if eigvects eq [] then
        W := VectorSpace(groundField, 0);
    else
        W := VectorSpaceWithBasis(eigvects);
    end if;
    return W;
end function;

function e(M, n, i : socle := false)
    /*
    Parameters: M : Rep(S_n),
                n : Nat, >= 3
                i : ground field
    */
    G := Group(M);
    H := n gt 3
        select sub<G | [G!(n, n-1)*G.1, G.2]>
        else sub<G | [G.2]>; // When  n eq 3

    groundField := Field(M);
    p := Characteristic(groundField);
    //Restrict M to H
    V := Restriction(M, H);
    // Get JM element
    r := Representation(M);
    r_res := Representation(V);
    x := JM(n, G, r);
    // Force JM element into an endomorphism of V
    x_forced := AHom(V, V)!x;

    // Compute generalised eigenspace
    W := generalisedEigenspace(x_forced, i);
    if Dimension(W) eq 0 then
        ActionMatrices := [Matrix(groundField, 0, 0, []) : i in [1..#Generators(H)]];
    else
        B := Basis(W);
        //Get matrices describing the action of generators of H
        ActionMatrices := [];
        for j := 1 to #Generators(H) do
            // Initialise empty sequence of columns of matrix of action of
            // j-th generator of H
            matrix_j_cols := [];
            for k := 1 to #B do
                // Let j-th generator of H act on k-th basis elt of W
                w_act := r_res(H.j)*Transpose(Matrix(B[k]));
                // Express in the given basis of W
                col_k := Coordinates(W, Vector(w_act));
                matrix_j_cols := Append(matrix_j_cols, col_k);
            end for;
            // Transpose here because Magma wants rows
            action_matrix_j := Transpose(Matrix(matrix_j_cols));
            ActionMatrices := Append(ActionMatrices, action_matrix_j);
        end for;
    end if;
    output := GModule(H, ActionMatrices);
    return socle select Socle(output) else output;
end function;

function partitionOf(M, n)
    G := Group(M);
    if not IsIrreducible(M) then Error("Error in e: M is not irreducible"); end if;
    p := Characteristic(BaseRing(M));
    path := [];

    // Reduce as long as the group > 3
    while n gt 2 do
        for i := 0 to p-1 do
            resM := e(M,n,i : socle := true);
            if Dimension(resM) gt 0 then
                M := resM;
                Append(~path,i);
                break;
            end if;
        end for;
        n := n-1;
    end while;

    // For S2, there are only two cases
    if n eq 2 then
        f := Representation(M);
        G := Group(M);
        _,iso := IsIsomorphic(Sym(2),G);
        isGensId := &and[IsOne(f(iso(Sym(2)!gen))): gen in Generators(Sym(2))];
        if isGensId then
            Append(~path,1); // Trivial
        else
            Append(~path,p-1); // Sign
        end if;
    end if;
    path := path cat [0];

    partition := [];
    for j in Reverse(path) do
        partition := iSocleInductionPartition(partition,j,p);
    end for;
    return partition;
end function;


function run_experiment(n, p)
    /*
    Parameters: n : Nat
    Initialise G = Sym(n) and H = Sym(n-1) and run abov, e code
        on irreducibles of G
    */


    G := Sym(n);
    H := sub<G|[G.2, G!(n, n-1)*G.1]>;
    Irr := IrreducibleModules(G, GF(p));

    for j := 1 to n do
        for i := 0 to p-1 do
            printf "i=%o, j=%o\n", i, j;
            print(e(Irr[j], G, H, n, i));
            print("-----------\n");
        end for;
    end for;
end function;



n := 7;
p := 2;
G := Sym(n);
Irr := IrreducibleModules(G, GF(p));

for i := 1 to #Irr do
    printf "i = %o\n",i;
    print partitionOf(Irr[i], n);
    print "-----";
end for; 

function MakeSymNModule(M, n)
    G := Group(M);
    isIso, _ := IsIsomorphic(G, Sym(n));
    if isIso eq false then Error("M is not a S_n module."); end if;
    r := Representation(M);
    // Get action generators of the group acting on M
    gen_1 := r(G.1);
    gen_2 := r(G.2);
    // Initialise "clean" Sym(n) module with the same action
    V := GModule(Sym(n), [gen_1, gen_2]);
    return V;
end function;

function OTIFunctor(M: use_centraliser:=false)
    G := Group(M);
    F := CoefficientRing(M);
    p := Characteristic(F);
    pCycle := G!(1,2);
    for i:=2 to p-1 do
        pCycle := G!(i,i+1) * pCycle;
        // the order of multiplication is flipped in magma for some reason
    end for;
    if use_centraliser eq true then
        H := Centralizer(G,pCycle);
    else
        // Use the "right-most" S_{n-p}
        g := Identity(G);
        for i := 1 to p do
            g := g * G!(i, i+1);
        end for;
        // 1st generator = cycle, 2nd generator = transposition.
        H := sub<G|G.1 * g, G!(p+1, p+2)>;
    end if;
    f := Representation(M);
    R := Restriction(M,H);

    x := f(G!1) - f(pCycle);
    phi := AHom(R,R)!x;

    output := [];
    for i:=1 to p-1 do
        phiPower := function (i) return i ne 0 select &*[phi : j in [1..i]] else AHom(R,R)!(f(G!1)); end function;
        OTI_i := quo<Kernel(phi) meet Image(phiPower(i-1)) | Kernel(phi) meet Image(phiPower(i))>;
        Append(~output, OTI_i);
    end for;
    return output;
end function;

function IdentifyFactors(M, n)
    M_clean := MakeSymNModule(M, n);
    if Dimension(M_clean) eq 0 then
        return [];
    else
        return [partitionOf(F, n) : F in CompositionFactors(M_clean)];
    end if;
end function;

function RunAllSimples(n, p)
    G := Sym(n);
    output := [];
    Irr := IrreducibleModules(G, GF(p));
    for X in Irr do
        // Identify partition of X.
        part_X := partitionOf(X, n);
        OTI_Output := OTIFunctor(X);
        composition_factors := [IdentifyFactors(M, n-p) : M in OTI_Output];
        Append(~output, <part_X, composition_factors>);
    end for;
    return output;
end function;

// ---------------------------------

// REQUIRES IHecke

if false then

AttachSpec("IHecke/IHecke.spec");

function RootOfUnity(C, k)
    return Exp(2 * Pi(C) * C.1 / k);
end function;

function EvalAt(X, v)
    /*
    Arguments: X : IHkeAlgStd
               v : ComplexField
    Evaluates the Laurent polynomials in the expression of X at v.
    */

    supp, coeffs := Support(X);
    outCoeffs := [];
    for i -> w in coeffs do
        coeffEval := Evaluate(coeffs[i], v);
        Append(~outCoeffs, coeffEval);
    end for;
    return outCoeffs;
end function;

function ReprEvalAt(X, v)
    supp, _ := Support(X);
    outCoeffs := EvalAt(X, v);
    for i->x in supp do
        // Looks super ugly but Magma is being a pos and won't let me format
        printf "%o * %o", C!outCoeffs[i], supp[i];
        if not i eq #supp then
            printf " + ";
        end if;
    end for;
    printf "\n";
    return true;
end function;

// ReprEvalAt((H.1 + H!v)^2, RootOfUnity(C, 4));

ell := 3;
W := CoxeterGroup(GrpFPCox, "A" cat IntegerToString(ell - 1));
HAlg := IHeckeAlgebra(W);
H := StandardBasis(HAlg);
L<v> := BaseRing(H);
C<i> := ComplexField();

T := H.0;
for i := 1 to ell - 1 do
    T := T * (H.i + H!v);
    //T := T * H.i;
end for;
//T := T + H!v;
T := T^ell;


P = PolynomialRing(ComplexField());
q := P!(1+5*x+4*x^2+x^3);
roots := Roots(q);
for r in roots do
    print "---";
    print "plus";
    print r;
    print ReprEvalAt(T, Sqrt(r[1]));
    print "minus"; 
    print ReprEvalAt(T, -Sqrt(r[1]));
end for;

//elt<P | Reverse(Eltseq(coeffs[1]))>;

end if;
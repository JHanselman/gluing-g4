QQ:=Rationals();
R<a11, a12, a21, a22, a31, a32, q001, q002, q012,  q101,q102, q111, q112>:=PolynomialRing(QQ,13);
q0:=Matrix(R, [[0,q001, q002], [q001, 0, q012], [q002, q012,1]]  );
q1:=Matrix(R, [[1,q101, q102], [q101, q111, q112], [q002, q012,0]]);


mods:=[1,a11,a12,1,a21,a22,1,a31,a32];
A := Transpose(Matrix(3,3,[1/el : el in mods]));
Ainv:=A^-1;
lambdas :=Ainv*Matrix(3,1,[BaseRing(Parent(Ainv)) | -1,-1,-1]);

mods_mat := [[mods[i], mods[i+1], mods[i+2]] : i in [1,4,7]];
L:=DiagonalMatrix(Eltseq(lambdas));
B := Matrix(3,3,mods)*L;
Binv := B^(-1);
ks:=Binv*Matrix(3,1,[BaseRing(Parent(Binv)) | -1,-1,-1]);
bitangents := [];
bitangents := [ [R | 1, 0, 0], [R | 0,1,0], [R | 0,0,1], [R | 1,1,1]];
bitangents cat:= mods_mat;

a1:=mods[1];a2:=mods[2];a3:=mods[3];
ap1:=mods[4];ap2:=mods[5];ap3:=mods[6];
as1:=mods[7];as2:=mods[8];as3:=mods[9];
F:=Parent(ks[1,1]);
P<x1,x2,x3>:=PolynomialRing(F,3);
M:=Matrix([[F|1,1,1],[ks[1,1]*a1,ks[1,1]*a2,ks[1,1]*a3],[ks[2,1]*ap1,ks[2,1]*ap2,ks[2,1]*ap3]]);
Mb:=Matrix([[F|1,1,1],[1/a1,1/a2,1/a3],[1/ap1,1/ap2,1/ap3]]);
U:=-Mb^(-1)*M;
u0:=U[1];
u1:=U[2];
u2:=U[3];
u0:=u0[1]*x1+u0[2]*x2+u0[3]*x3;
u1:=u1[1]*x1+u1[2]*x2+u1[3]*x3;
u2:=u2[1]*x1+u2[2]*x2+u2[3]*x3;
Quart:=(x1*u0+x2*u1-x3*u2)^2-4*x1*u0*x2*u1;
den:=Lcm([Denominator(coeff): coeff in Coefficients(Quart)]);
P1<x1,x2,x3>:=PolynomialRing(R,3);
Quart:=P1!(Quart*den);

bitangents cat:= [Coefficients(el) : el in [u0, u1, u2]];
CC3<t0,t1,t2> := Parent(u0);
bitangents cat:= [Coefficients(el) : el in [t0+t1+u2, t0+u1+t2, u0+t1+t2]];
// (3)
for i := 1 to 3 do
  new := u0/mods_mat[1,1] + ks[i,1]*(mods_mat[2,i]*t1 + mods_mat[3,i]*t2);
  Append(~bitangents, Coefficients(new));
end for;
// (4)
for i := 1 to 3 do
  new := u1/mods_mat[2,1] + ks[i,1]*(mods_mat[1,i]*t0 + mods_mat[3,i]*t2);
  Append(~bitangents, Coefficients(new));
end for;
// (5)
for i := 1 to 3 do
  new := u2/mods_mat[3,1] + ks[i,1]*(mods_mat[1,i]*t0 + mods_mat[2,i]*t1);
  Append(~bitangents, Coefficients(new));
end for;
// (6)
for i := 1 to 3 do
  new := u0/(1-ks[i,1]*mods_mat[2,i]*mods_mat[3,i]) + u1/(1-ks[i,1]*mods_mat[1,i]*mods_mat[3,i]) + u2/(1-ks[i,1]*mods_mat[1,i]*mods_mat[2,i]);
  Append(~bitangents, Coefficients(new));
end for;
for i := 1 to 3 do
  new := u0/(mods_mat[1,i]*(1-ks[i,1]*mods_mat[2,i]*mods_mat[3,i])) + u1/(mods_mat[2,i]*(1-ks[i,1]*mods_mat[1,i]*mods_mat[3,i])) + u2/(mods_mat[3,i]*(1-ks[i,1]*mods_mat[1,i]*mods_mat[2,i]));
  Append(~bitangents, Coefficients(new));
end for;



den:=[Lcm([Denominator(bi) : bi in bitangents[i]]): i in [1..28]];
bitangents:=[[R!(bitangents[i][j]*den[i]): j in [1..3]]: i in [1..28]];

Paux<q200, q201,q202,q211,q212, q300,q301,q302,q311,q312,q322>:=PolynomialRing(P1,11);

q2:=Matrix(Paux, [[q200,q201, q202], [q201, q211, q212], [q202, q212,0]]  );
q3:=Matrix(Paux, [[q300,q301, q302], [q301, q311, q312], [q302, q312,q322]]);
X:=Matrix(Paux, 3,1, [x1,x2,x3]);
LHs:=(Transpose(X)*ChangeRing(q0, Paux)*X*Transpose(X)*q3*X-Transpose(X)*ChangeRing(q1, Paux)*X*Transpose(X)*q2*X)[1,1];
mons:=MonomialsOfDegree(P1, 4);
Mat:=Matrix([[MonomialCoefficient(MonomialCoefficient(LHs, Paux.i), m): i in [1..11]]  : m in mons]);
SubMat:=Submatrix(Mat,1,1,11,11);
Cof:=Matrix([[Cofactor(SubMat, i, j): i in [1..11]]: j in [1..11]]);
det:=Determinant(SubMat);
RHs:=Matrix([[MonomialCoefficient(Quart, m)]  : m in mons]);
SubRHs:=Submatrix(RHs,1,1,11,1);
qcoeff:=Cof*SubRHs;
I:=Ideal(Eltseq(Mat*qcoeff-det*RHs));
S:=quo<R|I>;

q200v:=qcoeff[1,1];
q201v:=qcoeff[2,1];
q202v:=qcoeff[3,1];
q211v:=qcoeff[4,1];
q212v:=qcoeff[5,1];
q300v:=qcoeff[6,1];
q301v:=qcoeff[7,1];
q302v:=qcoeff[8,1];
q311v:=qcoeff[9,1];
q312v:=qcoeff[10,1];
q322v:=qcoeff[11,1];
q2:=Matrix(R, [[q200v,q201v, q202v], [q201v, q211v, q212v], [q202v, q212v,0]]  );
q3:=Matrix(R, [[q300v,q301v, q302v], [q301v, q311v, q312v], [q302v, q312v,q322v]]);

for i in [1..1] do
	bit:=Matrix(R, 3,1, bitangents[i]);
	Lhs:=[bit*Matrix(RSpace(R,3).j): j in [1..3]];
	Lhs:=[l+Transpose(l): l in Lhs];
	Mat:=Matrix([[Eltseq(l)[i]: i in [1,2,3,5,6,9]]: l in Lhs cat [q0, q1, q2, q3]]  );
end for;

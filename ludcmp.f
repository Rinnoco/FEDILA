       SUBROUTINE ludcmp(a,n,np,indx,d)
       INTEGER n,np,indx(n),NMAX
       REAL*8 d,TINY,a(np,np)
       PARAMETER (NMAX=500,TINY=1.0e-20)
C       Largest expected n, and a small number.
C      Given a matrix a(1:n,1:n), with physical dimension np by np
C      this routine replaces it by the LU decomposition of a rowwise
C      permutation of itself. a and n are input. a is output,arranged
C      as in equation (2.3.14) above; indx(1:n) is an output vector
C      that records the row permutation effected by the partial pivoting;
C      d is output as ±1 depending on whether the number of row interchanges
C      was even or odd, respectively. This routine is used in combination
C      with lubksb to solve linear equations or invert a matrix.
       INTEGER i,imax,j,k
       REAL*8 aamax,dum,sum,vv(NMAX) !vv stores the implicit scaling of each row.
       d=1.0 !No row interchanges yet.
       do i=1,n !Loop over rows to get the implicit scaling information.
         aamax=0.0
         do j=1,n
           if (abs(a(i,j)).gt.aamax) aamax=abs(a(i,j))
         enddo
         if (aamax.eq.0.) write(*,*) 'singular matrix in ludcmp'
C      No nonzero largest element.
         vv(i)=1./aamax !Save the scaling.
       enddo
       do j=1,n !This is the loop over columns of Crout's method.
         do i=1,j-1 !This is equation (2.3.12) except for i = j.
           sum=a(i,j)
           do k=1,i-1
           sum=sum-a(i,k)*a(k,j)
           enddo
          a(i,j)=sum
         enddo
         aamax=0. !Initialize for the search for largest pivot element.
         do i=j,n !This is i = j of equation (2.3.12) and i = j+1. . .N
C       of equation (2.3.13).
           sum=a(i,j)
           do k=1,j-1
           sum=sum-a(i,k)*a(k,j)
           enddo
           a(i,j)=sum
           dum=vv(i)*abs(sum) !Figure of merit for the pivot.
           if (dum.ge.aamax) then !Is it better than the best so far?
             imax=i
             aamax=dum
           endif
         enddo
         if (j.ne.imax)then !Do we need to interchange rows?
           do k=1,n !Yes, do so...
             dum=a(imax,k)
             a(imax,k)=a(j,k)
             a(j,k)=dum
           enddo
           d=-d !...and change the parity of d.
           vv(imax)=vv(j) !Also interchange the scale factor.
         endif
        indx(j)=imax
        if(a(j,j).eq.0.) a(j,j)= TINY
C       If the pivot element is zero the matrix is singular
C       (at least to the precision of the algorithm).
C       For some applications on singular matrices,
C       it is desirable to substitute TINY for zero.
       if(j.ne.n)then !Now, finally, divide by the pivot element.
         dum=1./a(j,j)
         do i=j+1,n
         a(i,j)=a(i,j)*dum
         enddo
       endif
       enddo !Go back for the next column in the reduction.
       return
       end

      subroutine lubksb(a,n,np,indx,b)
      integer n,np, indx(n)
      real*8 a(np,np),b(n)
      integer i,ii,j,ll
      real*8 sum
      ii=0
      do i=1,n
         ll=indx(i)
         sum=b(ll)
         b(ll)=b(i)
         if (ii.ne.0) then
            do j=ii,i-1
               sum = sum - a(i,j)*b(j)
            enddo
         else if (sum.ne.0.) then
            ii = i
         endif
         b(i)=sum
      enddo
      do i=n,1,-1
         sum=b(i)
         do j = i+1,n
            sum = sum - a(i,j)*b(j)
         enddo
         b(i) = sum/a(i,i)
      enddo
      return
      end

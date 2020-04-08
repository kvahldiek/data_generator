######
## Copyright 2020 Kai Vahldiek##
## Author
## Kai Vahldiek
## Departement of Computer Science, Ostfalia University of Applied Sciences
## D-38302, Wolfenbüttel, Germany
## Published under GNU General Public License##

#This program is free software: you can redistribute it and/or modify
#it under the terms of the GNU General Public License as published by
#the Free Software Foundation, either version 3 of the License, or
#(at your option) any later version.
#
#This program is distributed in the hope that it will be useful,
#but WITHOUT ANY WARRANTY; without even the implied warranty of
#MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#GNU General Public License for more details.
#
#You should have received a copy of the GNU General Public License
#along with this program.  If not, see <http://www.gnu.org/licenses/>.
######

tictoc::tic("Total")

#Required libraries
library(wordspace)
library(matrixcalc)
library(MASS)
library(mclust)

#######################
###############Beginn of needed functions#############

#Conversion of the correlation matrix - spearman  to pearson correlation
#for all spearman values in the matrix the respective pearson value is calculated
spearman.to.pearson <- function(spearmat){
  pearsonmat<-matrix(0,nrow(spearmat),ncol(spearmat))
  for (i in 1:nrow(spearmat)){
    for (j in 1:ncol(spearmat)){
      pearsonmat[i,j] <- 2*sin((spearmat[i,j]*pi)/6)
      }
  }
  return(pearsonmat)
}

#Conversion of the correlation matrix - kendall correlation to pearson correlation
#for all kendall values in the matrix the respective pearson value is calculated
kendall.to.pearson <- function(kendallmat){
  pearsonmat<-matrix(0,nrow(kendallmat),ncol(kendallmat))
  for (i in 1:nrow(kendallmat)){
    for (j in 1:ncol(kendallmat)){
        pearsonmat[i,j] <- sin((kendallmat[i,j]*pi)/2)
    }
  }
  return(pearsonmat)
}


##Matrix approximation
#Normalisation of the matrix
functionnormalize<-function(v){                     
  norm<-1/(colNorms(v, method = "euclidean", p = 2))
  normal<- v %*% diag(norm) 
  return(normal)
}

#create positive semidefinite Matrix
make.psd.matrix <- function(x){
  mat <- matrix(x,nrow=sqrt(length(x))) 
  mat <- functionnormalize(mat)
  return(t(mat) %*% mat)
}

#Define errorfunction
#calculate the difference, missing values are allowed
errorfunction<-function(m,a){
  diff<-sum((m-a)^2, na.rm = TRUE) 
  return(diff)
}

#target function for optimization based on the PSD matrix
objfunc <- function(x,target.matrix=NULL){
  mat <- make.psd.matrix(x)
  return(errorfunction(mat,target.matrix))
}

#own method to create the initial matrix
#find the maximum value in each row and column; all other elemtens are 0.
create.init.matrix <- function(mat) {
  dimm <- nrow(mat)
  diag(mat)<-0
  mat[lower.tri(mat)]<-0
  init.mat<-matrix(diag(dimm),dimm,dimm)
  
  while (sum(mat, na.rm = TRUE) != 0) {
    maxpos<-which(mat==mat[which.max(abs(mat))], arr.ind = TRUE)
    rowmax<-maxpos[1,1]
    colmax<-maxpos[1,2]
    init.mat[rowmax,colmax]<-mat[which.max(abs(mat))]
    
    for (i in 1:dimm){
      mat[rowmax,]<-0
      mat[,colmax]<-0
    }
  }
  
  init.mat[lower.tri(init.mat)]<-t(init.mat)[lower.tri(init.mat)]
  return(init.mat)
}

#method for matrix approximation used the own method
approx.mat <- function(target.matrix){ 
  x <- create.init.matrix(target.matrix)
  result <- optim(x, objfunc,target.matrix=target.matrix)
  return(make.psd.matrix(result$par))
}

#create random symmetric matrix
#generate a random symmetric matrix with missing values
generate.random.symmetric.matrix <- function(dimm,prob.na=0){
  dimm2 <- dimm*dimm
  mat <- matrix(runif(dimm2,min=-1,max=1),nrow=dimm)
  na.mat <- matrix(sample(c(TRUE,FALSE),dimm2,replace=T,prob=c(prob.na,1-prob.na)),nrow=dimm)
  mat[na.mat] <- NA
  mat[1,1] <- 1
  for (i in 2:dimm){
    mat[i,i] <- 1
    for (j in (1:(i-1))){
      mat[i,j] <- mat[j,i]
    }
  }
  return(mat)
}

#create random positive semidefinite matrix
#generate a random positive semidefinite matrix with missing values
generate.random.psd.matrix <- function(dimm,prob.na=0){ 
  dimm2 <- dimm*dimm
  mat <- make.psd.matrix(rnorm(dimm2))
  na.mat <- matrix(sample(c(TRUE,FALSE),dimm2,replace=T,prob=c(prob.na,1-prob.na)),nrow=dimm)
  mat[na.mat] <- NA
  mat[1,1] <- 1
  for (i in 2:dimm){
    mat[i,i] <- 1
  }
  return(mat)
}


#Data transformation
#Generate normal distribution
generate.normal.cdf <- function(mu=0,sigma=1){
  return(function(x){return(pnorm(x,mean=mu,sd=sigma))})
}

#Generate a mixture distribution consisting of multiple distributions (here: normal distributions)
generate.mixture.cdf <- function(cdfs,probs=NULL){
  coeffs <- probs
  if (is.null(probs)){
    coeffs <- rep(1,length(cdfs))
  }
  s <- sum(coeffs)
  coeffs <- coeffs/s
  
  f <- function(x){
    y <- 0
    for (i in 1:length(cdfs)){
      y <- y + cdfs[[i]](x)*coeffs[i]
    }
    return(y)
  }
  return(f)
}

#Auxiliary functions for the data transformation
#Quantile function
quantile.cdf <- function(perc,cdf,a=NULL,b=NULL,precision.x=0.000001,precision.y=0.000001){
  f <- function(x){
    return(cdf(x)-perc)
  }
  aa <- a
  if (is.null(a)){
    aa <- -.Machine$double.xmax
  }
  bb <- b
  if (is.null(a)){
    bb <- .Machine$double.xmax
  }
  return(bisection(f,aa,bb,precision.x=precision.x,precision.y=precision.y))
}

#Bisection function
bisection <- function(f,a,b,precision.x=0.000001,precision.y=0.000001){ 
  aa <- a 
  bb <- b
  f.a <- f(aa)
  f.b <- f(bb)
  s.a <- sign(f.a)
  s.b <- sign(f.b)
  root <- (bb+aa)/2
  while(bb-aa>precision.x & abs(f.a-f.b)>precision.y){ 
    f.root <- f(root)
    s.root <- sign(f.root)
    if (s.root==s.a){
      aa <- root
      f.a <- f.root  
    }else{
      bb <- root
      f.b <- f.root 
    }
    root <- (bb+aa)/2      
  }
  return(root)
}

#Transformation to a cumulative distribution function(CDF)
to.cdf <- function(x,cdf,a=NULL,b=NULL,precision.x=0.000001,precision.y=0.000001){
  qcdf <- function(y){
    return(quantile.cdf(y,cdf,a=a,b=b,precision.x=precision.x,precision.y=precision.y))
  }
  qcdf.v <- Vectorize(qcdf) 
  return(qcdf.v(pnorm(x))) 
}

###############End of needed function###############

#
#
#
#
#
#
#
#
#
#
#
#
#
#
#
#
#
#
#
############## Start of Application example  #######
#Approximate the original correlations of the Irisdataset
mat <- cor(iris[,-5],method = "spearman")
mat_approx <- approx.mat(spearman.to.pearson(mat))
colnames(mat_approx) <- c("Sepal.Length","Sepal.Width","Petal.Length","Petal.Width")
rownames(mat_approx) <- c("Sepal.Length","Sepal.Width","Petal.Length","Petal.Width")

#Generaet the data set based on the approximate correlations 
means <- rep(c(0),length(iris)-1)
irisdata <- mvrnorm(150,mu=means,Sigma=mat_approx)

#Information about the distribution of the first variable from the irisdataset
iris1 <- Mclust(iris[,1],modelNames="V") #Mixture model for the variable
iris1.means <- iris1$parameters$mean        ### Mean value
iris1.sigmasq <- iris1$parameters$variance$sigmasq     ### Variance
iris1.pro <- iris1$parameters$pro         ### Proportion of the total distribution

#Information about the distribution of the second variable from the irisdataset
iris2 <- Mclust(iris[,2],modelNames="V") 
iris2.means <- iris2$parameters$mean        
iris2.sigmasq <- iris2$parameters$variance$sigmasq
iris2.pro <- iris2$parameters$pro

#Information about the distribution of the third variable from the irisdataset
iris3 <- Mclust(iris[,3],modelNames="V") 
iris3.means <- iris3$parameters$mean       
iris3.sigmasq <- iris3$parameters$variance$sigmasq    
iris3.pro <- iris3$parameters$pro        

#Information about the distribution of the fourth variable from the irisdataset
iris4 <- Mclust(iris[,4],modelNames="V")
iris4.means <- iris4$parameters$mean
iris4.sigmasq <- iris4$parameters$variance$sigmasq
iris4.pro <- iris4$parameters$pro 

#Generate the data for each variable with the respective properties
#the first variable is created by a normal distribution
iris1.cdf <- generate.normal.cdf(iris1.means,sqrt(iris1.sigmasq))
iris1.result.cdf <- as.matrix(to.cdf(irisdata[,1],iris1.cdf,precision.x = 0.000001,precision.y = 0.000001))

#the second variable is created by a normal distribution
iris2.cdf <- generate.normal.cdf(iris2.means,sqrt(iris2.sigmasq))
iris2.result.cdf <- as.matrix(to.cdf(irisdata[,2],iris2.cdf,precision.x = 0.000001,precision.y = 0.000001))

#the third variable is created by a mixture distribution with two normal distributions
iris3.cdfs.vector <- c(generate.normal.cdf(iris3.means[1],sqrt(iris3.sigmasq[1])),generate.normal.cdf(iris3.means[2],sqrt(iris3.sigmasq[2])))
iris3.cdf <- generate.mixture.cdf(iris3.cdfs.vector, probs = c(iris3.pro[1],iris3.pro[2]))
iris3.result.cdf <- as.matrix(to.cdf(irisdata[,3],iris3.cdf,precision.x = 0.000001,precision.y = 0.000001))

#the fourth variable is created by a mixture distribution with two normal distributions
iris4.cdfs.vector <- c(generate.normal.cdf(iris4.means[1],sqrt(iris4.sigmasq[1])),generate.normal.cdf(iris4.means[2],sqrt(iris4.sigmasq[2])))
iris4.cdf <- generate.mixture.cdf(iris4.cdfs.vector, probs = c(iris4.pro[1],iris4.pro[2]))
iris4.result.cdf <- as.matrix(to.cdf(irisdata[,4],iris4.cdf,precision.x = 0.000001,precision.y = 0.000001))

#the wohle artifical data set
irisdata.cdf <- cbind(iris1.result.cdf,iris2.result.cdf,iris3.result.cdf,iris4.result.cdf)

#Plot the original and artifical data set
windowsFonts(TimesNewRoman  = windowsFont("Times New Roman"))
par(family = "TimesNewRoman")
plot(iris[,-5])
colnames(irisdata.cdf) <- c("Sepal.Length","Sepal.Width","Petal.Length","Petal.Width")
plot(as.data.frame(irisdata.cdf))

############## End of Application example  #######
tictoc::toc()
## Copyright 2020 Kai Vahldiek##
## Published under GNU General Public License##
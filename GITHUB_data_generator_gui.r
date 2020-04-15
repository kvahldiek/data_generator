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
library(shiny)  
library(MASS)
library(rhandsontable)
library(matrixcalc)
library(wordspace)

ui <- fluidPage(
  tags$head(
    tags$style(HTML("
      .shiny-output-error-validation {
        color: red;
        font-size: 20px;
      }
    "))
  ),
  sidebarPanel(
    #Time zone for generating data
    numericInput("RowNumber","RowNumber",10,min = 2),
    br(),
    #List of steps to produce sugar
    radioButtons("process","Process",c("Washing"="washing",
                                       "Slicing"="slicing",
                                       "Extraction"="extraction",
                                       "Purification"="purification",
                                       "Evaporation"="evaporation",
                                       "Crystalization"="crystalization",
                                       "Centrifugation"="centrifugation",
                                       "Cooling"="cooling"))
    
  ),
  mainPanel(
    tabsetPanel(
      #Enter the parameters required to create the data
      tabPanel(h3("Production process"),
               sidebarPanel(
                 uiOutput("setting")
               ),
               sidebarPanel(
                 uiOutput("ForChange")
               )
      ),
      #Display Data
      tabPanel(h3("Generated data"),
               mainPanel(
                 uiOutput("datatable")
               )
      )
    )
  )
)

server <- shinyServer(function(input,output) {
  
  Sugar <- matrix()
  Maxvector <- vector()
  
  #Custom csv file read function
  myReadcsv <- function(str){
    temp <- read.csv(str)
    rownames(temp) <- temp[,1]
    return(temp[,-1])
  }
  #Custom matrix symmetry test
  symmetrictest <- function(tmatrix){
    if (any(is.na(tmatrix)) || !is.symmetric.matrix(tmatrix))
      return(FALSE)
    else
      return(TRUE)
  }
  
  
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
        mat[colmax,]<-0
        mat[,rowmax]<-0
        mat[,colmax]<-0
      }
    }
    
    init.mat[lower.tri(init.mat)] = t(init.mat)[lower.tri(init.mat)]
    return(init.mat)
  }
  
  #method for Cholesky decomposition
  create.chol.vec <- function(init.mat) {
    chol.mat <- chol(init.mat)
    chol.vec <- as.vector(chol.mat)
  }
  
  #method for matrix approximation used the own method
  approx.mat <- function(target.matrix){
    x <- create.chol.vec(create.init.matrix(target.matrix))
    result <- optim(x, objfunc,target.matrix=target.matrix)
    return(make.psd.matrix(result$par))
  }
  
  
  #Data transformation
  #generate normal cdf (1)
  generate.normal.cdf <- function(mu=0,sigma=1){
    return(function(x){return(pnorm(x,mean=mu,sd=sigma))})
  }
  
  #generate lognormal cdf (2)
  generate.lognormal.cdf <- function(mu.log=0,sigma.log=1,shift=0){
    return(function(x){return(plnorm(x-shift,meanlog=mu.log,sdlog=sigma.log))})
  }
  
  #generate exp cdf (3)
  generate.exp.cdf <- function(rate=1){
    return(function(x){return(pexp(x,rate=rate))})
  }
  
  #generate t cdf (4)
  generate.t.cdf <- function(df=1){ #df >0
    return(function(x){return(pt(x,df=df))})
  }
  
  #generate chisquare cdf (5)
  generate.chisquare.cdf <- function(df=1){ #df >0
    return(function(x){return(pchisq(x,df=df))})
  }

  #generate beta cdf (6)
  generate.beta.cdf <- function(shape1=1,shape2=2){ 
    return(function(x){return(pbeta(x,shape1=shape1,shape2=shape2))})
  }
  
  #generate gamma cdf (7)
  generate.gamma.cdf <- function(shape=1,rate=2){ 
    return(function(x){return(pgamma(x,shape=shape,rate=rate))})
  }
  
  #Generate a mixture distribution consisting of multiple distributions
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
  
  #bisection
  bisection <- function(f,a,b,precision.x=0.000001,precision.y=0.000001){ 
    
    aa <- a 
    bb <- b
    f.a <- f(aa)
    f.b <- f(bb)
    s.a <- sign(f.a)
    s.b <- sign(f.b)
    #
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
  
  
  #Washing
  output$washing <- renderUI({
    tagList(
      checkboxGroupInput("variables", label = h3("Select variable(s)"), 
                         choices = c("Weight" = "weight", 
                                     "Level" = "level", 
                                     "Water" = "water",
                                     "Velocity" = "velocity",
                                     "Energy" = "energy",
                                     "Flow" = "flow",
                                     "Rate" = "rate"
                         ),
                         selected = c("weight","level")),
      uiOutput("washing1")
    )
  })
  
  #Slicing
  output$slicing <-renderUI(
    tagList(
      checkboxGroupInput("variables", label = h3("Select variable(s)"), 
                         choices = c("Velocity" = "velocity", 
                                     "Vibration" = "vibration", 
                                     "Energy" = "energy",
                                     "Flow amount" = "flow",
                                     "Flow rate" = "rate"
                                     
                         ),
                         selected = c("velocity","vibration"))
    )
  )
  
  #Extraction
  output$extraction <- renderUI(
    tagList(
      checkboxGroupInput("variables", label = h3("Select variable(s)"), 
                         choices = c("Temperature of water" = "temperature", 
                                     "Level of the machine" = "level", 
                                     "pH-Value " = "phvalue",
                                     "Concentration chemical substances (Amn, K, Na, P)" = "concentration",
                                     "Flow amount" = "flow",
                                     "Flow rate" = "rate"
                         ),
                         selected = c("temperature","level"))
    )
  )
  
  #Purification
  output$purification <- renderUI(
    tagList(
      checkboxGroupInput("variables", label = h3("Select variable(s)"), 
                         choices = c("Temperature of water" = "temperature", 
                                     "Level of the machine" = "level", 
                                     "pH-Value " = "phvalue",
                                     "Concentration chemical substances (Amn, K, Na, P)" = "concentration",
                                     "Flow amount" = "flow",
                                     "Flow rate" = "rate"
                         ),
                         selected = c("flow","rate"))
    )
  )
  
  #Evaporation
  output$evaporation <- renderUI(
    tagList(
      checkboxGroupInput("variables", label = h3("Select variable(s)"), 
                         choices = c("Temperature" = "temperature", 
                                     "Flow rate steam" = "flowRateSteam", 
                                     "Pressure steam" = "pressure",
                                     "Energy" = "energy",
                                     "Level of the machine" = "level",
                                     "Flow amount" = "flowAmount",
                                     "Flow rate" = "rate"
                         ),
                         selected = c("flowRateSteam","level"))
    )
  )
 
  #Crystalization
  output$crystalization <- renderUI(
    tagList(
      checkboxGroupInput("variables", label = h3("Select variable(s)"), 
                         choices = c("Temperature" = "temperature", 
                                     "Density" = "density", 
                                     "Energy" = "energy",
                                     "Level of the machine" = "level",
                                     "Flow amount" = "flow",
                                     "Flow rate" = "rate",
                                     "Size of the sugar particle" = "size"
                         ),
                         selected = c("energy","level"))
    )
  )
 
  #Centrifugation
  output$centrifugation <- renderUI(
    tagList(
      checkboxGroupInput("variables", label = h3("Select variable(s)"), 
                         choices = c("Energy" = "energy", 
                                     "Level of the machine" = "level",
                                     "Velocity of the machine" = "velocity",
                                     "Pressure water" = "pressure",
                                     "Vibration of the machine" = "vibration",
                                     "Size of the sugar particle" = "size",
                                     "Sugar colour" = "colour"
                         ),
                         selected = c("energy","level"))
    )
  )
 
  #Cooling
  output$cooling <- renderUI(
    tagList(
      checkboxGroupInput("variables", label = h3("Select variable(s)"), 
                         choices = c("Inlet temperature" = "inletTemperature", 
                                     "Real temperature" = "realTemperature" 
                         ),
                         selected = c("inletTemperature","realTemperature"))
    )
  )
  
  
  
  #Starting from the input date range, the UI starts working
   observeEvent(input$process,{
      output$ForChange <- renderUI(
        ""
      ) 
     
      output$inserttext <- renderUI(
        ""
      )
      
      output$checktext <- renderUI(
        ""
      )
      
      output$changetext <- renderUI(
        ""
      )
     
      output$datatable <- renderText(
        "Creating~~~~~~"
      )
    })
    
    #Display different UIs based on step names
    output$setting <- renderUI({
      tagList(
        switch(input$process,
               washing=uiOutput("washing"),
               slicing=uiOutput("slicing"),
               extraction=uiOutput("extraction"),
               purification=uiOutput("purification"),
               evaporation=uiOutput("evaporation"),
               crystalization=uiOutput("crystalization"),
               centrifugation=uiOutput("centrifugation"),
               cooling=uiOutput("cooling")),
        selectInput("correlation","Correlation",c("Spearman"="Spearman",
                                                  "Kendall"="Kendall")),
        uiOutput("checkresult"),
        h4("Correlation matrix (Please enter values between -1 and 1)"),
        rHandsontableOutput("tablecreate"),
        br(),
        actionButton("approximate","approximate matrix"),
        br(),
        uiOutput("checktext"),
        br()
      )
    })
    
    observeEvent({input$correlation
                  input$variables},{
      
      output$inserttext <- renderUI(
        ""
      )
      
      output$checktext <- renderUI(
        ""
      )
      
      output$changetext <- renderUI(
        ""
      )
      
      #Number of selected elements
      leng <- length(input$variables)
      #Selected element name
      variablenames <- input$variables
      #Initial matrix generation
      DF <- matrix(c(0),ncol = leng,nrow = leng)
      
      for (i in c(1:ncol(DF))){
        DF[i,i]=1
      }
      
      output$tablecreate <- renderRHandsontable({
       
        i <- 1
        DF <- as.data.frame(DF)
        k<-rhandsontable(DF, 
                         colHeaders = variablenames,
                         rowHeaders = variablenames,
                         stretchH = "all") %>%
          hot_cols(format = "0.000")
        
        #Set the bottom left (including the diagonal) to read-only
        while (i <= ncol(DF)){
          j <-1
          while (j <= i) {
            k <- hot_cell(k,i,j,readOnly = TRUE)
            j <- j+1
          }
          i <- i+1
        }
        k <- hot_validate_numeric(k,cols=c(1:ncol(DF)),min=-1,max=1)
        k
      })
    })
    
    #button check
    observeEvent(input$approximate,{
      
      #Selected element name
      variablenames <- input$variables
      #Number of selected elements
      leng <- length(variablenames)
      #Extract data from rhandsontable
      
      tempmatrix <- hot_to_r(input$tablecreate)
      tempmatrix <- data.matrix(tempmatrix)
      
      #Determine whether the check button takes effect by judging whether the matrix is symmetrical or empty.
      if (!symmetrictest(tempmatrix)){
        #1. Make the matirx symmetric
        tempmatrix[lower.tri(tempmatrix)]<-t(tempmatrix)[lower.tri(tempmatrix)]
        #2. Correction of the matrix
        if (input$correlation == "Spearman"){
          tempmatrix <- spearman.to.pearson(tempmatrix)
        } else if (input$correlation == "Kendall"){
          tempmatrix <- kendall.to.pearson(tempmatrix)
        }
        
        #3. Approximation of the matrix
        tempmatrix <- approx.mat(tempmatrix)
        tempmatrix <- data.frame(tempmatrix)
        output$tablecreate <- renderRHandsontable({
          rhandsontable(tempmatrix,
                        readOnly = TRUE,
                        colHeaders = variablenames,
                        rowHeaders = variablenames,
                        stretchH = "all")%>%
            hot_cols(format = "0.000")
        })
        
      } else {
        tempmatrix <- data.frame(tempmatrix)
        output$tablecreate <- renderRHandsontable({
          rhandsontable(tempmatrix,
                        readOnly = TRUE,
                        colHeaders = variablenames,
                        rowHeaders = variablenames,
                        stretchH = "all")%>%
            hot_cols(format = "0.000")
        })
      }
     
      output$checktext <- renderUI({
        validate(need(symmetrictest(data.matrix(tempmatrix)),"Sorry, something of check is wrong."),
                 errorClass = "myClass")
        HTML(paste(tags$span(style="color:green; font-size:20px", "Matrix successfully approximated")))
      })
     
      #Column length
      leng <- length(input$variables)
      #Column name vector
      variablenames <- input$variables
      #Get the mean vector
      means <- c(0)
      i <- 2
      means <- rep(c(0),leng)
      
      #Create data
      if (symmetrictest(data.matrix(tempmatrix))){
        Sugar <- mvrnorm(input$RowNumber,mu=means,Sigma = tempmatrix,empirical = TRUE)
        colnames(Sugar)=variablenames
        Sugar <<- Sugar
      }
      else
        Sugar <<- NULL
      
      
      #Negative numerical processing (absolute value)
      if (!is.null(Sugar)){
        
        Sugar <<- Sugar
        #Record maximum
        i <- 1
        while (i <= ncol(Sugar)) {
          Maxvector <-c(Maxvector[1:i],Sugar[which.max(Sugar[,i]),i])
          i <- i + 1
        }
        
        Maxvector <- Maxvector[-1]
        Maxvector <<- Maxvector
        
      }
        
      
      #Write data to the "csv" file
      if (!is.null(Sugar)){
        switch(input$process,
               washing=write.csv(Sugar,"Washing.csv"),
               slicing=write.csv(Sugar,"Slicing.csv"),
               extraction=write.csv(Sugar,"Extraction.csv"),
               purification=write.csv(Sugar,"Purification.csv"),
               evaporation=write.csv(Sugar,"Evaporation.csv"),
               crystalization=write.csv(Sugar,"Crystalization.csv"),
               centrifugation=write.csv(Sugar,"Centrifugation.csv"),
               cooling=write.csv(Sugar,"Cooling.csv"))
        
        output$datatable <- renderTable(
          rownames = TRUE,
          colnames = TRUE,
          Sugar
        )
      }
      
     
      
      #Change function UI integration
      output$ForChange <- renderUI({
        changevariables <- colnames(Sugar)
        tagList(
          h3("Data transformation"),
          selectInput("ChangeVariable","Change variable",changevariables),
          selectInput("ChangeWay","Change distribution",c("Normal"="Normal",
                                                          "Lognormal"="Lognormal",
                                                          "Exp"="Exp",
                                                          "T"="T",
                                                          "Chisquare"="Chisquare",
                                                          "Beta"="Beta",
                                                          "Gamma"="Gamma",
                                                          "Mixture"="Mixture")),
          uiOutput("VarForChange"),
          actionButton("Change","transform data"),
          uiOutput("changetext"),
          br(),
          br(),
          uiOutput("outlierinsert"),
          actionButton("insert","insert outlier"),
          uiOutput("inserttext")
        )
      })
      
      output$outlierinsert <- renderUI({
        variables <- colnames(Sugar)
        checkboxGroupInput("Outlier","One outlier per variable",variables)
      })
      
      #Method of generating data
      output$VarForChange <- renderUI({
        switch(input$ChangeWay,
               Normal=uiOutput("Normal"),
               Lognormal=uiOutput("Lognormal"),
               Exp=uiOutput("Exp"),
               T=uiOutput("T"),
               Chisquare=uiOutput("Chisquare"),
               Beta=uiOutput("Beta"),
               Gamma=uiOutput("Gamma"),
               Mixture=uiOutput("Mixture"))
      })
      
      #Normal
      output$Normal <- renderUI(
        tagList(
          numericInput("mean","Mean normal",7),
          numericInput("sd","Sigma normal",1)
        )
      )
      
      #Lognormal
      output$Lognormal <- renderUI(
        tagList(
          numericInput("meanlog","Mean log",2),
          numericInput("sdlog","Sigma log",3),
          numericInput("logshift","Shift log",1)
        )
      )
      
      #Exp
      output$Exp <- renderUI(
        numericInput("exprate","Rate exp",1/2)
      )
      
      #T
      output$T <- renderUI(
        numericInput("tdf","Df t",2)
      )
      
      #Chisquare
      output$Chisquare <- renderUI(
        numericInput("chisquaredf","Df chisquare",2)
      )
      
      #Beta
      output$Beta <- renderUI(
        tagList(
          numericInput("betashape1","Shape1 beta",2),
          numericInput("betashape2","Shape2 beta",3)
        )
      )
      
      #Gamma
      output$Gamma <- renderUI(
        tagList(
          numericInput("gammashape","Shape gamma",1),
          numericInput("gammarate","Rate gamma",4)
        )
      )
      
      #Mixture
      output$Mixture <- renderUI({
        tagList(
          sliderInput("numbernorm","The number of normal",min = 2,max = 5,2,step = 1),
          rHandsontableOutput("Mixture1")
        )
      })
      
      output$Mixture1 <- renderRHandsontable({
        names <- c("norm1")
        MAS <- matrix(c(0,1,0.5),nrow = 3,ncol = input$numbernorm)
        for (i in c(2:input$numbernorm)){
          names <- c(names,paste("norm",i,sep = ""))
        }
        MAS <- data.frame(MAS)
        rhandsontable(
          MAS,
          colHeaders = names,
          rowHeaders = c("mean","sd","prob")
        )
      })
      
    })
    
    #Button insert
    observeEvent(input$insert,{
      
      #Maximum recovery
      i <- 1
      while (i <= ncol(Sugar)){
        Sugar[which.max(Sugar[,i]),i] <<- Maxvector[i]
        i <- i+1
      }
      
      #Insert outlier
      for (i in input$Outlier){
        Sugar[which.max(Sugar[,i]),i]<<-max(Sugar[,i])*1.2
      }
      
      #Update ".csv" document
      if (input$process == "washing"){
        String <- "Washing.csv"
      } else if (input$process == "slicing"){
        String <- "Slicing.csv"
      } else if (input$process == "extraction"){
        String <- "Extraction.csv"
      } else if (input$process == "purification"){
        String <- "Purification.csv"
      } else if (input$process == "evaporation"){
        String <- "Evaporation.csv"
      } else if (input$process == "crystalization"){
        String <- "Crystalization.csv"
      } else if (input$process == "centrifugation"){
        String <- "Centrifugation.csv"
      } else if (input$process == "cooling"){
        String <- "Cooling.csv"
      }
      
      write.csv(Sugar,String)
      
      #Insert Button's response text
      output$inserttext <- renderUI({
        Sys.sleep(2)
        HTML(paste(tags$span(style="color:green; font-size:20px", "Outliers successfully insert")))
      })
      
      output$datatable <- renderTable(
        rownames = TRUE,
        colnames = TRUE,
        Sugar
      )
    })
    
    #Button Change
    observeEvent(input$Change,{
      if (input$process == "washing"){
        String <- "Washing.csv"
      } else if (input$process == "slicing"){
        String <- "Slicing.csv"
      } else if (input$process == "extraction"){
        String <- "Extraction.csv"
      } else if (input$process == "purification"){
        String <- "Purification.csv"
      } else if (input$process == "evaporation"){
        String <- "Evaporation.csv"
      } else if (input$process == "crystalization"){
        String <- "Crystalization.csv"
      } else if (input$process == "centrifugation"){
        String <- "Centrifugation.csv"
      } else if (input$process == "cooling"){
        String <- "Cooling.csv"
      }
      
      
      #Base is the standard normal distribution for data transformation
      
      #data transformation
      if (input$ChangeWay == "Normal"){
        cdfs.vector <- generate.normal.cdf(input$mean,input$sd)
        Sugar[,paste(input$ChangeVariable)] <- to.cdf(Sugar[,paste(input$ChangeVariable)],cdfs.vector,precision.x = 0.000001,precision.y = 0.000001)
      } else if (input$ChangeWay == "Lognormal"){
        cdfs.vector <- generate.lognormal.cdf(input$meanlog,input$sdlog,input$logshift)
        Sugar[,paste(input$ChangeVariable)] <- to.cdf(Sugar[,paste(input$ChangeVariable)],cdfs.vector,precision.x = 0.000001,precision.y = 0.000001)
      } else if (input$ChangeWay == "Exp"){
        cdfs.vector <- generate.exp.cdf(input$exprate)
        Sugar[,paste(input$ChangeVariable)] <- to.cdf(Sugar[,paste(input$ChangeVariable)],cdfs.vector,precision.x = 0.000001,precision.y = 0.000001)
      } else if (input$ChangeWay == "T"){
        cdfs.vector <- generate.t.cdf(input$tdf)
        Sugar[,paste(input$ChangeVariable)] <- to.cdf(Sugar[,paste(input$ChangeVariable)],cdfs.vector,precision.x = 0.000001,precision.y = 0.000001)
      } else if (input$ChangeWay == "Chisquare"){
        cdfs.vector <- generate.chisquare.cdf(input$chisquaredf)
        Sugar[,paste(input$ChangeVariable)] <- to.cdf(Sugar[,paste(input$ChangeVariable)],cdfs.vector,precision.x = 0.000001,precision.y = 0.000001)
      } else if (input$ChangeWay == "Beta"){
        cdfs.vector <- generate.beta.cdf(input$betashape1,input$betashape2)
        Sugar[,paste(input$ChangeVariable)] <- to.cdf(Sugar[,paste(input$ChangeVariable)],cdfs.vector,precision.x = 0.000001,precision.y = 0.000001)
      } else if (input$ChangeWay == "Gamma"){
        cdfs.vector <- generate.gamma.cdf(input$gammashape,input$gammarate)
        Sugar[,paste(input$ChangeVariable)] <- to.cdf(Sugar[,paste(input$ChangeVariable)],cdfs.vector,precision.x = 0.000001,precision.y = 0.000001)
      } else if (input$ChangeWay == "Mixture"){
        MASes <- hot_to_r(input$Mixture1)
        MASes <- data.matrix(MASes)
        
        cdfs.vector <- generate.normal.cdf(MASes[1,1],MASes[2,1])
        
        cdfs.probs <- MASes[3,1]
        
        for (i in c(2:input$numbernorm))
          cdfs.vector <- c(cdfs.vector,generate.normal.cdf(MASes[1,i],MASes[2,i]))
        
        for (i in c(2:input$numbernorm)) 
          cdfs.probs <- c(cdfs.probs,MASes[3,i])
        
        mixture.cdf <- generate.mixture.cdf(cdfs.vector,cdfs.probs)
        Sugar[,paste(input$ChangeVariable)] <- to.cdf(Sugar[,paste(input$ChangeVariable)],mixture.cdf,precision.x = 0.000001,precision.y = 0.000001)
      }
      
      write.csv(Sugar,String)
      Sugar <<- myReadcsv(String)
      #Record maximum
      Maxvector[paste(input$ChangeVariable)] <- Sugar[which.max(Sugar[,paste(input$ChangeVariable)]),paste(input$ChangeVariable)]
      Maxvector <<- Maxvector
      
      output$datatable <- renderTable(
        rownames = TRUE,
        colnames = TRUE,
        Sugar
      )
      
      output$changetext <- renderUI({
        Sys.sleep(2)
        HTML(paste(tags$span(style="color:green; font-size:20px", "Variable successfully transformed")))
      })
    })
    
    observeEvent(input$ChangeWay,{
      output$changetext <- renderUI(
        ""
      )
    })
    
    observeEvent(input$ChangeVariable,{
      output$changetext <- renderUI(
        ""
      )
    })
  
})

shinyApp(ui = ui,server = server) 

tictoc::toc()
## Copyright 2020 Kai Vahldiek##
## Published under GNU General Public License##
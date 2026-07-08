library(shiny)
library(quadprog)
library(tseries)

DesStatFun=function(z){
  Res=NULL
  Res[1]=min(z)
  Res[2]=median(z)
  Res[3]=max(z)
  Res[4]=mean(z)
  Res[5]=sd(z)
  return(Res)
}

FourierResiduals=function(y,x,k=1,case=2){
  y=as.numeric(y)
  x=as.matrix(x)
  Tn=length(y)
  if(nrow(x)!=Tn)stop("Length mismatch")
  tvec=1:Tn
  sinv=sin(2*pi*k*tvec/Tn)
  cosv=cos(2*pi*k*tvec/Tn)
  if(case==2){
    X=cbind(1,sinv,cosv,x)
  }else if(case==3){
    X=cbind(1,tvec,sinv,cosv,x)
  }else{
    stop("case must be 2 or 3")
  }
  df=data.frame(y=y,X)
  colnames(df)=c("y",paste0("v",1:ncol(X)))
  form=as.formula(paste0("y~",paste0(colnames(df)[-1],collapse="+")))
  m=lm(form,data=df)
  return(residuals(m))
}

addDeterministic=function(Z,det){
  n=nrow(Z)
  if(det=="none")return(Z)
  if(det=="const")return(cbind(1,Z))
  if(det=="trend")return(cbind(1,1:n,Z))
  stop("det must be none, const, or trend")
}

fitQP=function(Z,absZ,Yc,YL,YU,det){
  Z=addDeterministic(Z,det)
  absZ=abs(Z)
  k=ncol(Z)
  Daa=2*t(Z)%*%Z
  Dmat=rbind(
    cbind(Daa,matrix(0,k,k)),
    cbind(matrix(0,k,k),matrix(0,k,k))
  )+diag(1e-8,2*k)
  dvec=c(2*t(Z)%*%Yc,rep(0,k))
  G1=t(cbind(-Z,absZ))
  G2=t(cbind(Z,absZ))
  G3=t(cbind(matrix(0,k,k),diag(k)))
  Amat=cbind(G1,G2,G3)
  bvec=c(-YL,YU,rep(0,k))
  sol=solve.QP(Dmat,dvec,Amat,bvec)
  a=sol$solution[1:k]
  cpar=pmax(sol$solution[(k+1):(2*k)],0)
  list(a=a,c=cpar,det=det)
}

ForecastARDL=function(X_train,Y_train,X_test,p,q,det){
  max_pq=max(p,q)
  X_all=c(X_train,X_test)
  Y_all=c(Y_train,rep(NA,length(X_test)))
  
  buildZ=function(Y,X){
    Z=NULL
    for(t in (max_pq+1):length(Y)){
      Zt=NULL
      for(i in 1:p) Zt=c(Zt,Y[t-i])
      for(j in 0:q) Zt=c(Zt,X[t-j])
      Z=rbind(Z,Zt)
    }
    return(Z)
  }
  
  Z_train=buildZ(Y_train,X_train)
  Y_dep=Y_train[(max_pq+1):length(Y_train)]
  Z_train_det=addDeterministic(Z_train,det)
  fit=lm(Y_dep~Z_train_det-1)
  a=coef(fit)
  sig=sd(resid(fit))
  
  Yhat=rep(NA,length(X_test))
  YL=rep(NA,length(X_test))
  YU=rep(NA,length(X_test))
  
  for(h in 1:length(X_test)){
    t=length(Y_train)+h
    Zt=NULL
    for(i in 1:p) Zt=c(Zt,Y_all[t-i])
    for(j in 0:q) Zt=c(Zt,X_all[t-j])
    
    if(det=="none")Ztd=Zt
    if(det=="const")Ztd=c(1,Zt)
    if(det=="trend")Ztd=c(1,nrow(Z_train)+h,Zt)
    
    Yhat[h]=sum(Ztd*a)
    YL[h]=Yhat[h]-1.96*sig
    YU[h]=Yhat[h]+1.96*sig
    Y_all[t]=Yhat[h]
  }
  list(Yhat=Yhat,YL=YL,YU=YU)
}

ForecastFARDL=function(X_train,Y_train,X_test,fit,p,q,det){
  max_pq=max(p,q)
  X_all=c(X_train,X_test)
  Y_all=c(Y_train,rep(NA,length(X_test)))
  T_train=length(Y_train)-max_pq
  
  Yhat=rep(NA,length(X_test))
  YL=rep(NA,length(X_test))
  YU=rep(NA,length(X_test))
  
  for(h in 1:length(X_test)){
    t=length(Y_train)+h
    Zt=NULL
    for(i in 1:p) Zt=c(Zt,Y_all[t-i])
    for(j in 0:q) Zt=c(Zt,X_all[t-j])
    
    if(det=="none")Ztd=Zt
    if(det=="const")Ztd=c(1,Zt)
    if(det=="trend")Ztd=c(1,T_train+h,Zt)
    
    center=sum(Ztd*fit$a)
    spread=sum(abs(Ztd)*fit$c)
    
    Yhat[h]=center
    YL[h]=center-spread
    YU[h]=center+spread
    Y_all[t]=center
  }
  list(Yhat=Yhat,YL=YL,YU=YU)
}

TheilU=function(Y,Yhat){
  sqrt(mean((Y-Yhat)^2))/(sqrt(mean(Y^2))+sqrt(mean(Yhat^2)))
}

Coverage=function(Y,YL,YU){
  mean(Y>=YL & Y<=YU)
}

RMSE=function(Y,Yhat){
  sqrt(mean((Y-Yhat)^2))
}

DMFun=function(Y,Yhat1,Yhat2){
  e1=Y-Yhat1
  e2=Y-Yhat2
  d=e1^2-e2^2
  DM=mean(d)/sqrt(var(d)/length(d))
  pval=2*(1-pt(abs(DM),df=length(d)-1))
  c(DM=DM,p.value=pval)
}



######################الواجهة 
ui <- fluidPage(
  
  # =========================================
  # APPLICATION TITLE
  # =========================================
  
  titlePanel("Fuzzy ARDL Forecasting System"),
  
  tags$div(
    style = "
    color: purple;
    font-size: 18px;
    font-weight: bold;
    margin-left: 15px;
    margin-top: -10px;
    margin-bottom: 15px;
  ",
    "Powered by (Suliaman H.Jawad & Munaf Y.Hmood)"
  ),
  
  
  
  fluidRow(
    
    # =========================================
    # SIDEBAR PANEL
    # =========================================
    
    column(
      width = 3,
      
      wellPanel(
        
        h3("Model Controls"),
        
        actionButton(
          "run",
          "Run Models",
          class = "btn-primary btn-lg"
        ),
        
        br(), br(), br(),
        
        # =====================================
        # GENERAL SETTINGS
        # =====================================
        
 
        h4("Data Frequency"),
        p("Quarterly Time Series"),
        
        hr(),
        
        # =====================================
        # DATA SPLIT SETTINGS
        # =====================================
        
        h4("Data Split"),
        
        sliderInput(
          "train_ratio",
          "Training Sample (%)",
          min = 50,
          max = 95,
          value = 80,
          step = 1
        ),
        
        hr(),
        
        h4("Automatic Lag Selection"),
        
        numericInput(
          "max_lag_ardl",
          "Maximum ARDL Lag",
          value = 4,
          min = 1,
          max = 8
        ),
        
        checkboxInput(
          "auto_ardl",
          "Auto Select ARDL by AIC",
          value = FALSE
        ),
        
        br(),
        
        numericInput(
          "max_lag_fardl",
          "Maximum FARDL Lag",
          value = 4,
          min = 1,
          max = 8
        ),
        
        checkboxInput(
          "auto_fardl",
          "Auto Select FARDL by RMSE",
          value = FALSE
        ),
        
    
        
        
        
        
        # =====================================
        # ARDL SETTINGS
        # =====================================
        
        h4("ARDL Settings"),
        
        selectInput(
          "det_ardl",
          "ARDL Model Form",
          choices = c(
            "No Constant / No Trend" = "none",
            "Constant Only" = "const",
            "Constant and Trend" = "trend"
          ),
          selected = "trend"
        ),
        
        numericInput(
          "p_ardl",
          "ARDL Lag order of Y",
          value = 3,
          min = 1,
          max = 8
        ),
        
        numericInput(
          "q_ardl",
          "ARDL Lag order of X",
          value = 4,
          min = 0,
          max = 8
        ),
        
        hr(),
        
        # =====================================
        # FARDL-QP SETTINGS
        # =====================================
        
        h4("FARDL-QP Settings"),
        
        selectInput(
          "det_fardl",
          "FARDL Model Form",
          choices = c(
            "No Constant / No Trend" = "none",
            "Constant Only" = "const",
            "Constant and Trend" = "trend"
          ),
          selected = "trend"
        ),
        
        numericInput(
          "p_fardl",
          "FARDL Lag order of Y",
          value = 4,
          min = 1,
          max = 8
        ),
        
        numericInput(
          "q_fardl",
          "FARDL Lag order of X",
          value = 4,
          min = 0,
          max = 8
        )
      )
    ),
    
    # =========================================
    # MAIN CONTENT PANEL
    # =========================================
    
    column(
      width = 9,
      
      tabsetPanel(
        # =====================================
        # Data Summary
        # =====================================      
        tabPanel(
          "Data Summary",
          
          br(),
          
          h3("Descriptive Statistics and Variable Plots"),
          
          tableOutput("summary_stats"),
          
          br(),
          
          plotOutput("variables_plot", height = "500px"),
          
          br(),
          
          h3("Observed Data Table"),
          
          tableOutput("data_values_table")
        ),
        
        # =====================================
        # ACF,CCF
        # ===================================== 
        
        
        tabPanel(
          "ACF & CCF Analysis",
          
          br(),
          
          h2("Autocorrelation and Cross-Correlation Analysis"),
          
          br(),
          
          plotOutput("acf_ccf_plot", height = "650px")
        ),
        
        
        
        # =====================================
        # MODEL EVALUATION TAB
        # =====================================
        
        tabPanel(
          "Model Evaluation",
          
          br(),
          
          fluidRow(
            
            column(
              width = 6,
              
              h3("Comparison Table"),
              
              tableOutput("compareTable")
            ),
            
            column(
              width = 6,
              
              h3("Diebold-Mariano Test"),
              
              tableOutput("dmTable")
            )
          )
        ),
        
        # =====================================
        # KPSS TEST TAB
        # =====================================
        
        tabPanel(
          "KPSS Test",
          
          br(),
          
          h2("KPSS Stationarity Test"),
          
          br(),
          
          tableOutput("kpssTable")
        ),
        
        tabPanel(
          "Automatic Model Selection",
          
          br(),
          
          fluidRow(
            
            column(
              width = 6,
              h2("ARDL Selection by AIC"),
              tableOutput("ardlSelectionTable")
            ),
            
            column(
              width = 6,
              h2("FARDL-QP Selection by RMSE"),
              tableOutput("fardlSelectionTable")
            )
          )
        ),
        
        
        # =====================================
        # PARAMETER ESTIMATES TAB
        # =====================================
        
        tabPanel(
          "Parameter Estimates",
          
          br(),
          
          h2("Estimated Parameters"),
          
          br(),
          
          tableOutput("resTable")
        ),
        
        # =====================================
        # FORECAST PLOT TAB
        # =====================================
        
        tabPanel(
          "Forecast Plot",
          
          br(),
          
          h2("FARDL Estimation and Forecasting"),
          
          br(),
          
          plotOutput(
            "qpPlot",
            height = "750px",
            width = "100%"
          )
        ),
        
        # =====================================
        # OUT-OF-SAMPLE FORECAST TAB
        # =====================================
        
        tabPanel(
          "Out-of-Sample Forecasts",
          
          br(),
          
          h2("Complete Forecast Results"),
          
          br(),
          
          tableOutput("forecastTable")
        ),
        
        # =====================================
        # External Forecast
        # =====================================     
        tabPanel(
          "External Forecast",
          
          br(),
          
          h2("External Forecasting"),
          
          numericInput(
            "external_h",
            "Number of Forecasted Values for Y",
            value = 1,
            min = 1,
            max = 4,
            step = 1
          ),
          
          h3("Future Public Revenues Values"),
          
          fluidRow(
            column(3, numericInput("x_future_1", "X Forecast 1", value = NA)),
            column(3, numericInput("x_future_2", "X Forecast 2", value = NA)),
            column(3, numericInput("x_future_3", "X Forecast 3", value = NA)),
            column(3, numericInput("x_future_4", "X Forecast 4", value = NA))
          ),
          
          br(),
          
          h3("Forecasted Budget Surplus / Deficit"),
          
          tableOutput("externalForecastTable")
        )
      )
    )
  )
)
    
    
    
    
    
    
    
#############################################################البيانات والتشغيل 
server <- function(input, output, session) {
  
  observeEvent(input$run, {
    
    X <- c(28.716265, 26.375666, 30.674826, 28.000638,
           26.290853, 28.346808, 25.444804, 25.304158, 14.697552,
           16.306727, 16.511773, 18.954200, 6.980143, 15.435991,
           13.350322, 18.642814, 15.324487, 16.398606, 24.549812,
           21.063050, 21.431309, 23.936898, 31.115046, 30.086581,
           20.458173, 25.611431, 27.166525, 34.330866, 18.168104,
           9.914513, 10.358615, 24.758457, 17.311942, 22.605556,
           31.593736, 37.570230, 34.901964, 40.737365, 47.157174,
           38.900934, 27.236213, 27.072127, 41.539847, 39.833079,31.222753,34.698849,48.428137,26.424367,27.248764,34.755174, 29.843828 )
    
    Y <- c(11.928087, 1.476802, 2.136739, -8.647260,
           13.254903, 13.780045, 11.573110, -16.777661, 3.460424,
           -0.642614, -0.737602, -6.007471, -4.707486, -3.204968,
           -1.519991, -3.225722, 1.828321, 1.969864, 0.248302,
           -2.200647, 8.388422, 6.491370, 4.384894, 6.431959,
           2.028613, 5.216008, -0.457179, -10.943970, 0.790508,
           -4.062199, -10.021255, 0.410192, -0.131747, 1.928128,
           8.142723, -3.707299, 11.408643, 15.036579, 17.598418,
           0.694215, 4.568021, 1.939697, 11.083735, -24.345823,6.145711,1.52191,11.803225,-29.224086,-0.890668,6.182393,-13.420696)
    
    train_ratio <- input$train_ratio / 100
    
    n_total <- length(Y)
    
    train_end <- floor(n_total * train_ratio)
    
    X_train <- X[1:train_end]
    Y_train <- Y[1:train_end]
    
    X_test <- X[(train_end + 1):n_total]
    Y_test <- Y[(train_end + 1):n_total]
    # =====================================
    # DESCRIPTIVE STATISTICS
    # =====================================
    output$summary_stats <- renderTable({
      
      data.frame(
        Variable = c("Budget Surplus / Deficit", "Public Revenues"),
        
        Mean = c(
          mean(Y, na.rm = TRUE),
          mean(X, na.rm = TRUE)
        ),
        
        SD = c(
          sd(Y, na.rm = TRUE),
          sd(X, na.rm = TRUE)
        ),
        
        Min = c(
          min(Y, na.rm = TRUE),
          min(X, na.rm = TRUE)
        ),
        
        Max = c(
          max(Y, na.rm = TRUE),
          max(X, na.rm = TRUE)
        )
      )
      
    })
    
    
    # =====================================
    # VARIABLES PLOT
    # =====================================
    output$variables_plot <- renderPlot({
      
      par(
        mfrow = c(1,2),
        mar = c(5,5,4,2),
        cex.main = 1.4,
        cex.lab = 1.2,
        cex.axis = 1.1
      )
      
      # =====================================
      # Budget Surplus / Deficit
      # =====================================
      
      plot(
        Y,
        type = "l",
        col = "purple",
        lwd = 3,
        xlab = "Time",
        ylab = "Budget",
        main = "Budget Surplus / Deficit"
      )
      
      grid()
      
      
      # =====================================
      # Public Revenues
      # =====================================
      
      plot(
        X,
        type = "l",
        col = "darkgreen",
        lwd = 3,
        xlab = "Time",
        ylab = "Revenues",
        main = "Public Revenues"
      )
      
      grid()
      
    })
    
 ############################################DATA AS TABEL   
    
    
    output$data_values_table <- renderTable({
      
      start_year <- 2013
      start_quarter <- 1
      
      time_index <- paste0(
        start_year + ((seq_along(Y) - 1) %/% 4),
        " Q",
        ((seq_along(Y) - 1) %% 4) + 1
      )
      
      data.frame(
        Period = time_index,
        `Budget Surplus / Deficit` = round(Y, 4),
        `Public Revenues` = round(X, 4)
      )
      
    }, rownames = FALSE)   
    
    # =====================================
    # ACF AND CCF PLOTS
    # =====================================
    
    output$acf_ccf_plot <- renderPlot({
      
      par(
        mfrow = c(1,2),
        mar = c(4,4,3,1)
      )
      
      
      # =====================================
      # ACF FOR DEPENDENT VARIABLE (Y)
      # =====================================
      
      acf(
        Y_train,
        main = "ACF: Budget Surplus / Deficit (Y)",
        xlab = "Lag",
        ylab = "ACF"
      )
      
      
      # =====================================
      # CCF : X → Y
      # =====================================
      
      ccf(
        X_train,
        Y_train,
        main = "CCF: Public Revenues (X) → Budget Surplus / Deficit (Y)",
        xlab = "Lag",
        ylab = "CCF"
      )
      
    })
    

    # =====================================
    # KPSS FUNCTION
    # =====================================
    
    KPSS_Function <- function(series, type_test = "Level") {
      
      test <- kpss.test(series, null = type_test)
      
      stat <- as.numeric(test$statistic)
      
      critical_value <- ifelse(
        type_test == "Level",
        0.463,
        0.146
      )
      
      if(stat < critical_value){
        
        integration_order <- "I(0)"
        
      } else {
        
        d_series <- diff(series)
        
        test_diff <- kpss.test(d_series, null = type_test)
        
        stat_diff <- as.numeric(test_diff$statistic)
        
        if(stat_diff < critical_value){
          
          integration_order <- "I(1)"
          
        } else {
          
          integration_order <- "Non-Stationary"
        }
      }
      
      return(
        c(
          Statistic = round(stat,4),
          Critical = critical_value,
          Integration = integration_order
        )
      )
    }
    
    
    
    # =====================================
    # APPLY KPSS TEST
    # =====================================
    
    KPSS_X_Level <- KPSS_Function(X_train, "Level")
    
    KPSS_Y_Level <- KPSS_Function(Y_train, "Level")
    
    KPSS_X_Trend <- KPSS_Function(X_train, "Trend")
    
    KPSS_Y_Trend <- KPSS_Function(Y_train, "Trend")
    
    
    
    # =====================================
    # KPSS RESULTS TABLE
    # =====================================
    
    KPSS_Results <- data.frame(
      
      Variable = c(
        "Public Revenues (X)",
        "Budget Surplus / Deficit (Y)",
        "Public Revenues (X)",
        "Budget Surplus / Deficit (Y)"
      ),
      
      Test_Form = c(
        "Constant",
        "Constant",
        "Constant and Trend",
        "Constant and Trend"
      ),
      
      Statistic = c(
        KPSS_X_Level[1],
        KPSS_Y_Level[1],
        KPSS_X_Trend[1],
        KPSS_Y_Trend[1]
      ),
      
      Critical_Value_5pct = c(
        KPSS_X_Level[2],
        KPSS_Y_Level[2],
        KPSS_X_Trend[2],
        KPSS_Y_Trend[2]
      ),
      
      Order_of_Integration = c(
        KPSS_X_Level[3],
        KPSS_Y_Level[3],
        KPSS_X_Trend[3],
        KPSS_Y_Trend[3]
      )
      
    )

  
    
    ###################################################################AIC
    SelectBestARDL_AIC <- function(X_train, Y_train, det, max_lag){
      
      Results <- data.frame()
      
      for(p_try in 1:max_lag){
        for(q_try in 0:max_lag){
          
          max_pq_try <- max(p_try, q_try)
          
          Z_try <- NULL
          
          for(t in (max_pq_try + 1):length(Y_train)){
            
            Zt <- NULL
            
            for(i in 1:p_try){
              Zt <- c(Zt, Y_train[t - i])
            }
            
            for(j in 0:q_try){
              Zt <- c(Zt, X_train[t - j])
            }
            
            Z_try <- rbind(Z_try, Zt)
          }
          
          Y_dep_try <- Y_train[(max_pq_try + 1):length(Y_train)]
          Z_det_try <- addDeterministic(Z_try, det)
          
          fit_try <- lm(Y_dep_try ~ Z_det_try - 1)
          
          e <- resid(fit_try)
          nobs <- length(e)
          kpar <- length(coef(fit_try))
          
          AIC_EViews <- log(sum(e^2) / nobs) + (2 * kpar / nobs)
          
          Results <- rbind(
            Results,
            data.frame(
              p = p_try,
              q = q_try,
              AIC = AIC_EViews
            )
          )
        }
      }
      
      Results <- Results[order(Results$AIC), ]
      
      return(Results)
    } 
    
    # =========================================
    # FARDL AUTOMATIC SELECTION BY RMSE
    # =========================================

    SelectBestFARDL_RMSE <- function(
    X_train,
    Y_train,
    det,
    max_lag
    ){
      
      Results <- data.frame()
      
      for(p_try in 1:max_lag){
        
        for(q_try in 0:max_lag){
          
          max_pq_try <- max(p_try, q_try)
          
          buildZ_try <- function(Y, X){
            
            Z <- NULL
            
            for(t in (max_pq_try + 1):length(Y)){
              
              Zt <- NULL
              
              for(i in 1:p_try){
                Zt <- c(Zt, Y[t - i])
              }
              
              for(j in 0:q_try){
                Zt <- c(Zt, X[t - j])
              }
              
              Z <- rbind(Z, Zt)
            }
            
            return(Z)
          }
          
          Z_try <- buildZ_try(Y_train, X_train)
          Yc_try <- Y_train[(max_pq_try + 1):length(Y_train)]
          
          Ys_try <- 0.10 * abs(Yc_try)
          YL_try <- Yc_try - Ys_try
          YU_try <- Yc_try + Ys_try
          
          fit_try <- fitQP(
            Z_try,
            abs(Z_try),
            Yc_try,
            YL_try,
            YU_try,
            det
          )
          
          Z_det_try <- addDeterministic(Z_try, det)
          YC_try <- as.numeric(Z_det_try %*% fit_try$a)
          
          rmse_try <- RMSE(Yc_try, YC_try)
          
          Results <- rbind(
            Results,
            data.frame(
              p = p_try,
              q = q_try,
              RMSE = rmse_try
            )
          )
        }
      }
      
      Results <- Results[order(Results$RMSE), ]
      
      return(Results)
    } 
    
    
    
    det_ardl <- input$det_ardl
    p_ardl <- input$p_ardl
    q_ardl <- input$q_ardl
    
    if(input$auto_ardl == TRUE){
      
      ARDL_AIC_Table <- SelectBestARDL_AIC(
        X_train,
        Y_train,
        det = det_ardl,
        max_lag = input$max_lag_ardl
      )
      
      p_ardl <- ARDL_AIC_Table$p[1]
      q_ardl <- ARDL_AIC_Table$q[1]
      
    } else {
      
      ARDL_AIC_Table <- data.frame(
        p = p_ardl,
        q = q_ardl,
        AIC = NA
      )
    }
    
    
    
    det_fardl <- input$det_fardl
    p_fardl <- input$p_fardl
    q_fardl <- input$q_fardl
    
    if(input$auto_fardl == TRUE){
      
      FARDL_RMSE_Table <- SelectBestFARDL_RMSE(
        X_train,
        Y_train,
        det = det_fardl,
        max_lag = input$max_lag_fardl
      )
      
      p_fardl <- FARDL_RMSE_Table$p[1]
      q_fardl <- FARDL_RMSE_Table$q[1]
      
    } else {
      
      FARDL_RMSE_Table <- data.frame(
        p = p_fardl,
        q = q_fardl,
        RMSE = NA
      )
    }
    
    
    
    
    
    
    det <- det_fardl
    p <- p_fardl
    q <- q_fardl
    
    max_pq <- max(p, q)
    
    buildZ <- function(Y, X){
      Z <- NULL
      
      for(t in (max_pq + 1):length(Y)){
        Zt <- NULL
        
        for(i in 1:p){
          Zt <- c(Zt, Y[t - i])
        }
        
        for(j in 0:q){
          Zt <- c(Zt, X[t - j])
        }
        
        Z <- rbind(Z, Zt)
      }
      
      return(Z)
    }
    
    Z <- buildZ(Y_train, X_train)
    Yc <- Y_train[(max_pq+1):length(Y_train)]
    
    spreadScale <- 0.10
    Ys <- spreadScale * abs(Yc)
    YL <- Yc - Ys
    YU <- Yc + Ys
    absZ <- abs(Z)
    
    fitQ <- fitQP(Z, absZ, Yc, YL, YU, det)
    
    ARDL_out <- ForecastARDL(
      X_train,
      Y_train,
      X_test,
      p = p_ardl,
      q = q_ardl,
      det = det_ardl
    )
    QP_out <- ForecastFARDL(
      X_train,
      Y_train,
      X_test,
      fitQ,
      p = p_fardl,
      q = q_fardl,
      det = det_fardl
    )
    
    Compare <- matrix(NA, 2, 3)
    
    Compare[1,] <- c(
      RMSE(Y_test, ARDL_out$Yhat),
      TheilU(Y_test, ARDL_out$Yhat),
      Coverage(Y_test, ARDL_out$YL, ARDL_out$YU)
    )
    
    Compare[2,] <- c(
      RMSE(Y_test, QP_out$Yhat),
      TheilU(Y_test, QP_out$Yhat),
      Coverage(Y_test, QP_out$YL, QP_out$YU)
    )
    
    rownames(Compare) <- c("ARDL", "FARDL-QP")
    colnames(Compare) <- c("RMSE", "Theil_U", "Coverage")
    
    DM_ARDL_QP <- DMFun(Y_test, ARDL_out$Yhat, QP_out$Yhat)
    DM_Results <- rbind(ARDL_vs_FARDL_QP = DM_ARDL_QP)
    
    Z_det <- addDeterministic(Z, det)
    YC_Q <- Z_det %*% fitQ$a
    YS_Q <- abs(Z_det) %*% fitQ$c
    
    metrics <- function(Y, YL, YC, YU){
      RMSE <- sqrt(mean((Y - YC)^2))
      MAPE <- mean(abs((Y - YC) / Y))
      FD <- mean(YU - YL)
      c(RMSE = RMSE, MAPE = MAPE, FD = FD)
    }
    
    Res_Q <- metrics(Yc, YC_Q - YS_Q, YC_Q, YC_Q + YS_Q)
    
    if(det == "none"){
      detNames <- NULL
    } else if(det == "const"){
      detNames <- "Intercept"
    } else {
      detNames <- c("Intercept", "trend")
    }
    
    ParNames <- c(
      detNames,
      paste0("Y_L", 1:p),
      paste0("X_L", 0:q)
    )
    
    Res <- data.frame(
      Parameter = c(ParNames, "RMSE", "MAPE", "FD"),
      QP_a = c(as.numeric(fitQ$a), as.numeric(Res_Q)),
      QP_c = c(as.numeric(fitQ$c), NA, NA, NA)
    )
    
    output$compareTable <- renderTable({
      round(Compare, 4)
    }, rownames = TRUE)
    
    output$kpssTable <- renderTable({
      KPSS_Results
    }, rownames = FALSE)
    
    
    
    
    output$dmTable <- renderTable({
      round(DM_Results, 4)
    }, rownames = TRUE)
    
    output$resTable <- renderTable({
      Res
    }, rownames = FALSE)
    
    output$forecastTable <- renderTable({
      data.frame(
        Quarter = paste0("Q", 1:length(Y_test)),
        Actual = round(Y_test, 4),
        ARDL_Forecast = round(ARDL_out$Yhat, 4),
        FARDL_Forecast = round(QP_out$Yhat, 4),
        Lower_Bound = round(QP_out$YL, 4),
        Upper_Bound = round(QP_out$YU, 4),
        ARDL_Error = round(Y_test - ARDL_out$Yhat, 4),
        FARDL_Error = round(Y_test - QP_out$Yhat, 4)
      )
    }, rownames = FALSE)
    
    # =========================================
    # AUTOMATIC MODEL SELECTION TABLES
    # =========================================
    
    output$ardlSelectionTable <- renderTable({
      
      ARDL_AIC_Table
      
    }, rownames = FALSE)
    
    output$fardlSelectionTable <- renderTable({
      
      FARDL_RMSE_Table
      
    }, rownames = FALSE)
    
    # =========================================
    # FORECAST PLOT
    # =========================================
    
    output$qpPlot <- renderPlot({
      
      # =====================================
      # TIME SETTINGS
      # =====================================
      
      start_year <- 2013
      freq <- 4
      
      test_start_index <- train_end + 1
      
      test_start_year <- start_year + ((test_start_index - 1) %/% freq)
      
      test_start_quarter <- ((test_start_index - 1) %% freq) + 1
      
      split_time <- start_year + ((train_end - 1) / freq)
      
      
      # =====================================
      # TRAINING SERIES
      # =====================================
      
      Y_train_ts <- ts(
        Yc,
        start = c(2014,1),
        frequency = freq
      )
      
      
      # =====================================
      # TEST SERIES
      # =====================================
      
      Y_test_ts <- ts(
        Y_test,
        start = c(test_start_year, test_start_quarter),
        frequency = freq
      )
      
      
      # =====================================
      # IN-SAMPLE FITTED VALUES
      # =====================================
      
      YC_Q_num <- as.numeric(YC_Q)
      YS_Q_num <- as.numeric(YS_Q)
      
      YL_Q <- YC_Q_num - YS_Q_num
      YU_Q <- YC_Q_num + YS_Q_num
      
      YC_Q_ts <- ts(
        YC_Q_num,
        start = c(2014,1),
        frequency = freq
      )
      
      YL_Q_ts <- ts(
        YL_Q,
        start = c(2014,1),
        frequency = freq
      )
      
      YU_Q_ts <- ts(
        YU_Q,
        start = c(2014,1),
        frequency = freq
      )
      
      
      # =====================================
      # OUT-OF-SAMPLE FORECASTS
      # =====================================
      
      QP_hat_ts <- ts(
        QP_out$Yhat,
        start = c(test_start_year, test_start_quarter),
        frequency = freq
      )
      
      QP_L_ts <- ts(
        QP_out$YL,
        start = c(test_start_year, test_start_quarter),
        frequency = freq
      )
      
      QP_U_ts <- ts(
        QP_out$YU,
        start = c(test_start_year, test_start_quarter),
        frequency = freq
      )
      
      
      # =====================================
      # Y LIMITS
      # =====================================
      
      ylim_Q <- range(
        c(
          ts(Y, start = c(2013,1), frequency = freq),
          Y_test_ts,
          YL_Q_ts,
          YU_Q_ts,
          QP_L_ts,
          QP_U_ts
        ),
        na.rm = TRUE
      )
      
      
      # =====================================
      # MAIN PLOT
      # =====================================
      
      plot(
        ts(Y, start = c(2013,1), frequency = freq),
        type = "l",
        lwd = 2,
        col = "black",
        ylim = ylim_Q,
        xlab = "Time (Quarterly)",
        ylab = "Surplus / Deficit",
        main = "FARDL Estimation and Out-of-Sample Forecasting"
      )
      
      
      # =====================================
      # IN-SAMPLE ESTIMATION
      # =====================================
      
      lines(YC_Q_ts, lwd = 2, col = "darkgreen")
      
      lines(YL_Q_ts, lwd = 2, col = "brown", lty = 2)
      
      lines(YU_Q_ts, lwd = 2, col = "brown", lty = 2)
      
      
      # =====================================
      # OUT-OF-SAMPLE FORECAST
      # =====================================
      
      lines(Y_test_ts, lwd = 2, col = "black")
      
      lines(QP_hat_ts, lwd = 2, col = "blue", lty = 2)
      
      lines(QP_L_ts, lwd = 2, col = "red", lty = 3)
      
      lines(QP_U_ts, lwd = 2, col = "red", lty = 3)
      
      
      # =====================================
      # TRAIN / TEST SPLIT LINE
      # =====================================
      
      abline(
        v = split_time,
        lty = 3,
        lwd = 2,
        col = "gray40"
      )
      
      
      # =====================================
      # LEGEND
      # =====================================
      
      legend(
        "topleft",
        legend = c(
          "Actual",
          "Estimated Center",
          "Lower/Upper",
          "Forecast",
          "Forecast Bounds",
          "Train/Test Split"
        ),
        
        col = c(
          "black",
          "darkgreen",
          "brown",
          "blue",
          "red",
          "gray40"
        ),
        
        lty = c(1,1,2,2,3,3),
        
        lwd = 2,
        
        bty = "n"
      )
      
    })
    # =====================================
    # FINAL FULL-SAMPLE FARDL MODEL
    # =====================================
    
    Z_full <- buildZ(Y, X)
    
    Yc_full <- Y[(max_pq + 1):length(Y)]
    
    Ys_full <- 0.10 * abs(Yc_full)
    
    YL_full <- Yc_full - Ys_full
    
    YU_full <- Yc_full + Ys_full
    
    fitQ_full <- fitQP(
      Z_full,
      abs(Z_full),
      Yc_full,
      YL_full,
      YU_full,
      det
    )
    
    
    
    
    
    # =====================================
    # EXTERNAL FORECAST TABLE
    # =====================================
    
    output$externalForecastTable <- renderTable({
      
      h <- input$external_h
      
      X_future_all <- c(
        input$x_future_1,
        input$x_future_2,
        input$x_future_3,
        input$x_future_4
      )
      
      X_future <- X_future_all[1:h]
      
      if(any(is.na(X_future))){
        return(
          data.frame(
            Message = "Please enter the required future Public Revenues values."
          )
        )
      }
      
      External_Forecast <- ForecastFARDL(
        X,
        Y,
        X_future,
        fitQ_full,
        p = p_fardl,
        q = q_fardl,
        det = det_fardl
      )
      
      data.frame(
        Forecast_Number = paste0("Y Forecast ", 1:h),
        Public_Revenues_Input = round(X_future, 4),
        Forecasted_Budget_Surplus_Deficit = round(External_Forecast$Yhat, 4),
        Lower_Bound = round(External_Forecast$YL, 4),
        Upper_Bound = round(External_Forecast$YU, 4)
      )
      
    }, rownames = FALSE)
    
    
    
    
    
    
    
    
    
    
    
    
    
    
  })     # end observeEvent
  
}        # end server

shinyApp(ui = ui, server = server)








































# Practical Time Series Analysis


### 1. Time Series: An Overview and a Quick History
#### The History of Time Series in Diverse Applications
##### Medicine as a Time Series Problem
##### Forecasting Weather
##### Forecasting Economic Growth
##### Astronomy
#### Time Series Analysis Takes Off
#### The Origins of Statistical Time Series Analysis
#### The Origins of Machine Learning Time Series Analysis
#### More Resources

### 2. Finding and Wrangling Time Series Data
#### Where to Find Time Series Data
##### Prepared Data Sets
##### Found Time Series
#### Retrofitting a Time Series Data Collection from a Collection of Tables
##### A Worked Example: Assembling a Time Series Data Collection
##### Constructing a Found Time Series
#### Timestamping Troubles
##### Whose Timestamp?
##### Guesstimating Timestamps to Make Sense of Data
##### What’s a Meaningful Time Scale?
#### Cleaning Your Data
##### Handling Missing Data
##### Upsampling and Downsampling
##### Smoothing Data
#### Seasonal Data
#### Time Zones
#### Preventing Lookahead
#### More Resources

### 3. Exploratory Data Analysis for Time Series
#### Familiar Methods
##### Plotting
##### Histograms
##### Scatter Plots
#### Time Series–Specific Exploratory Methods
##### Understanding Stationarity
##### Applying Window Functions
##### Understanding and Identifying Self-Correlation
##### Spurious Correlations
#### Some Useful Visualizations
##### 1D Visualizations
##### 2D Visualizations
##### 3D Visualizations
#### More Resources

### 4. Simulating Time Series Data
#### What’s Special About Simulating Time Series?
##### Simulation Versus Forecasting
#### Simulations in Code
##### Doing the Work Yourself
##### Building a Simulation Universe That Runs Itself
##### A Physics Simulation
#### Final Notes on Simulations
##### Statistical Simulations
##### Deep Learning Simulations
#### More Resources

### 5. Storing Temporal Data
#### Defining Requirements
##### Live Data Versus Stored Data
#### Database Solutions
##### SQL Versus NoSQL
##### Popular Time Series Database and File Solutions
#### File Solutions
##### NumPy
##### Pandas
##### Standard R Equivalents
##### Xarray
#### More Resources

### 6. Statistical Models for Time Series
#### Why Not Use a Linear Regression?
#### Statistical Methods Developed for Time Series
##### Autoregressive Models
##### Moving Average Models
##### Autoregressive Integrated Moving Average Models
##### Vector Autoregression
##### Variations on Statistical Models
#### Advantages and Disadvantages of Statistical Methods for Time Series
#### More Resources

### 7. State Space Models for Time Series
#### State Space Models: Pluses and Minuses
#### The Kalman Filter
##### Overview
##### Code for the Kalman Filter
#### Hidden Markov Models
##### How the Model Works
##### How We Fit the Model
##### Fitting an HMM in Code
#### Bayesian Structural Time Series
##### Code for bsts
#### More Resources

### 8. Generating and Selecting Features for a Time Series
#### Introductory Example
#### General Considerations When Computing Features
##### The Nature of the Time Series
##### Domain Knowledge
##### External Considerations
#### A Catalog of Places to Find Features for Inspiration
##### Open Source Time Series Feature Generation Libraries
##### Domain-Specific Feature Examples
#### How to Select Features Once You Have Generated Them
#### Concluding Thoughts
#### More Resources

### 9. Machine Learning for Time Series
#### Time Series Classification
##### Selecting and Generating Features
##### Decision Tree Methods
#### Clustering
##### Generating Features from the Data
##### Temporally Aware Distance Metrics
##### Clustering Code
#### More Resources

### 10. Deep Learning for Time Series
#### Deep Learning Concepts
#### Programming a Neural Network
##### Data, Symbols, Operations, Layers, and Graphs
#### Building a Training Pipeline
##### Inspecting Our Data Set
##### Steps of a Training Pipeline
#### Feed Forward Networks
##### A Simple Example
##### Using an Attention Mechanism to Make Feed Forward Networks More Time-Aware
#### CNNs
##### A Simple Convolutional Model
##### Alternative Convolutional Models
#### RNNs
##### Continuing Our Electric Example
##### The Autoencoder Innovation
#### Combination Architectures
#### Summing Up
#### More Resources

### 11. Measuring Error
#### The Basics: How to Test Forecasts
##### Model-Specific Considerations for Backtesting
#### When Is Your Forecast Good Enough?
#### Estimating Uncertainty in Your Model with a Simulation
#### Predicting Multiple Steps Ahead
##### Fit Directly to the Horizon of Interest
##### Recursive Approach to Distant Temporal Horizons
##### Multitask Learning Applied to Time Series
#### Model Validation Gotchas
#### More Resources

### 12. Performance Considerations in Fitting and Serving Time Series Models
#### Working with Tools Built for More General Use Cases
##### Models Built for Cross-Sectional Data Don’t “Share” Data Across Samples
##### Models That Don’t Precompute Create Unnecessary Lag Between
##### Measuring Data and Making a Forecast
#### Data Storage Formats: Pluses and Minuses
##### Store Your Data in a Binary Format
##### Preprocess Your Data in a Way That Allows You to “Slide” Over It
#### Modifying Your Analysis to Suit Performance Considerations
##### Using All Your Data Is Not Necessarily Better
##### Complicated Models Don’t Always Do Better Enough
##### A Brief Mention of Alternative High-Performance Tools
#### More Resources

### 13. Healthcare Applications
#### Predicting the Flu
##### A Case Study of Flu in One Metropolitan Area
##### What Is State of the Art in Flu Forecasting?
#### Predicting Blood Glucose Levels
##### Data Cleaning and Exploration
##### Generating Features
##### Fitting a Model
#### More Resources

### 14. Financial Applications
#### Obtaining and Exploring Financial Data
#### Preprocessing Financial Data for Deep Learning
##### Adding Quantities of Interest to Our Raw Values
##### Scaling Quantities of Interest Without a Lookahead
##### Formatting Our Data for a Neural Network
#### Building and Training an RNN
#### More Resources

### 15. Time Series for Government
#### Obtaining Governmental Data
#### Exploring Big Time Series Data
##### Upsample and Aggregate the Data as We Iterate Through It
##### Sort the Data
#### Online Statistical Analysis of Time Series Data
##### Remaining Questions
##### Further Improvements
#### More Resources

### 16. Time Series Packages
#### Forecasting at Scale
##### Google’s Industrial In-house Forecasting
##### Facebook’s Open Source Prophet Package
#### Anomaly Detection
##### Twitter’s Open Source AnomalyDetection Package
#### Other Time Series Packages
#### More Resources

### 17. Forecasts About Forecasting
#### Forecasting as a Service
#### Deep Learning Enhances Probabilistic Possibilities
#### Increasing Importance of Machine Learning Rather Than Statistics
#### Increasing Combination of Statistical and Machine Learning Methodologies
#### More Forecasts for Everyday Life

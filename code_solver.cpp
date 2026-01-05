#include <fstream>
#include <iostream>
#include <stdlib.h>
#include <set>
#include <string>
#include <string.h>
#include <vector>
#include <iterator>  
#include <algorithm>
#include <list>
#include <time.h>
#include <cmath>
#include <cfloat>
#include <iomanip>
#include <sstream>

double dwellPerPassenger;
double dwellPerStop;
double excessWeight;
double maxJourneyTime;

using namespace std;

//Define the information kept on each shape
struct STOP {  
   double x;			//Longitude
   double y;			//Lattitude
   string label;		//Name of the stop
   bool required;
};

struct ADDR {
	double x;			//Longitude
	double y;			//Lattitude
	string label;		//Name of the address
	int numPass;		//Number of passengers
};

struct SOL {
	vector<vector<int> > items;			//List of stops on each route
	vector<vector<int> > W;				//Number boarding in each instance of a stop in items
	vector<vector<int> > routeOfStop;	//Gives the route number of each stop (could be blank or have multiple elements)
	vector<bool> stopUsed;				//Tells us whether the stop is being used or not
	vector<int> assignedTo;				//Tells us, for each address, the assigned bus stop (must be the closest available)
	vector<int> numBoarding;			//The total number of students who are boarding at each stop
	vector<double> routeLen;			//The total length (in seconds) of each bus's route, including dwell times
	vector<int> passInRoute;			//The total numer of students assigned to each route
	vector<bool> hasOutlier;			//True if route i has one or more outlier stop, false otherwise
	vector<vector<int> > posInRoute;	//Element i, j indicates the position of stop i in route j (set to -1 if i is not in j)
	vector<vector<bool> > commonStop;	//Element i, j is true if bus-routes i and j share a common stop, false otherwise
	double cost;						//Cost of the solution (sum of route lengths (in seconds), with weighting)
	double costWalk;					//Cost of the solution in terms of total walk time of all passengers
	int numFeasibleRoutes;				//Number of feasible routes in the solution (i.e. <= the specified maximum route length)
	int numEmptyRoutes;					//Number of empty routes in the solution (if any)
	int numUsedStops;					//Number of used stops
	int solSize;						//Total number of times all stops are used
	int numRoutesWithOutliers;			//Number of routes containing outlier stops
};

struct EVALINFO {
	bool flippedX;					//Tells us whether X section should be flipped
	bool flippedI;					//Tells us whether I section should be flipped
	double innerX;					//Total travel time of X section
	double innerI;					//Total travel time of I section
	double innerXF;					//Total travel time of X section in reverse direction
	double innerIF;					//Total travel time of I section in reverse direction
	double dwellXSection;			//Total dwell time of X section
	double dwellISection;			//Total dwell time of I section
	int passXSection;				//Total passengers in X Section
	int passISection;				//Total passengers in I Section
};

extern vector<STOP> stops;
extern vector<ADDR> addresses;
extern vector<bool> isOutlier;
extern vector<vector<double> > dDist;
extern vector<vector<double> > dTime;
extern vector<vector<double> > wDist;
extern vector<vector<double> > wTime;
extern vector<vector<int> > stopAdjList;
extern vector<vector<int> > addrAdjList;
extern vector<vector<bool> > addrStopAdj;
extern int totalPassengers, maxBusCapacity;
extern double maxWalkDist;
extern double minEligibilityDist;
extern string distUnits;
extern double dwellPerPassenger;
extern double dwellPerStop;
extern double excessWeight;
extern double maxJourneyTime;
double maxJourneyTimeMins = 45.0;

//Functions for sorting an array of stop indexes according to their distance from addr (or stop)
int partitionStopsByDist(vector<int> &A, int left, int right, int who, int addr) {
	for (int i = left; i<right; ++i) {
		if (wTime[addr][A[i]] <= wTime[addr][who]) {
			swap(A[i], A[left]);
			left++;
		}
	}
	return left - 1;
}

void qSortStopsByDist(vector<int> &A, int left, int right, int addr) {
	if (left >= right) return;
	int middle = left + (right - left) / 2;
	swap(A[middle], A[left]);
	int midpoint = partitionStopsByDist(A, left + 1, right, A[left], addr);
	swap(A[left], A[midpoint]);
	qSortStopsByDist(A, left, midpoint, addr);
	qSortStopsByDist(A, midpoint + 1, right, addr);
}

int partitionAddressesByDist(vector<int> &A, int left, int right, int who, int stop) {
	for (int i = left; i<right; ++i) {
		if (wTime[A[i]][stop] <= wTime[who][stop]) {
			swap(A[i], A[left]);
			left++;
		}
	}
	return left - 1;
}

void qSortAddressesByDist(vector<int> &A, int left, int right, int stop) {
	if (left >= right) return;
	int middle = left + (right - left) / 2;
	swap(A[middle], A[left]);
	int midpoint = partitionAddressesByDist(A, left + 1, right, A[left], stop);
	swap(A[left], A[midpoint]);
	qSortAddressesByDist(A, left, midpoint, stop);
	qSortAddressesByDist(A, midpoint + 1, right, stop);
}

void trim(string &str) {
	//Trims any whitespce and commas from the left and right of the string.
	if (str.length() == 0) return;
	int l = 0, r = str.length() - 1;
	while (str[l] == ' ' || str[l] == ',' || str[l] == '\t') {
		l++;
	}
	while (str[r] == ' ' || str[r] == ',' || str[r] == '\t') {
		r--;
	}
	str = str.substr(l, r - l + 1);
}

istream& readInput(istream &cin) {
	//Reads in the input file
	int i, j, x, y, numStops, numAddresses, numWalks;
	double d, t;
	string temp;

	totalPassengers = 0;

  cin >> numStops;
	cin >> numAddresses;
  cin >> numWalks;
	distUnits = "kms";
	cin >> minEligibilityDist;
  cin >> maxWalkDist;
  cin >> maxJourneyTimeMins >> maxBusCapacity >> dwellPerPassenger >> dwellPerStop;

	stops.resize(numStops);
	addresses.resize(numAddresses);
	dTime.resize(numStops, vector<double>(numStops));
	dDist.resize(numStops, vector<double>(numStops));
	wTime.resize(numAddresses, vector<double>(numStops, DBL_MAX));
	wDist.resize(numAddresses, vector<double>(numStops, DBL_MAX));
	
	//Now read information about the stops
	for (i = 0; i < numStops; i++) {
   cin >> stops[i].x >> stops[i].y;
		stops[i].required = false;
	}

	//And similalrly for the addresses
	for (i = 0; i < numAddresses; i++) {
    cin >> addresses[i].x >> addresses[i].y;
    cin >> addresses[i].numPass;
		totalPassengers += addresses[i].numPass;
	}

	//Now read the distances between all stop pairs
	for (i = 0; i < numStops; i++) {
		for (j = 0; j < numStops; j++) {
      cin >> dDist[i][j];
		}
	}
  for (i = 0; i < numStops; i++) {
    for (j = 0; j < numStops; j++) {
      cin >> dTime[i][j];
    }
  }
	//Read information about a walk time distance pair
	// for (i = 0; i < numWalks; i++) {
  //   cin >> x >> y;
  //   cin >> wDist[x][y] >> wTime[x][y];
	// }
  for (int i = 0; i < numAddresses; i++) {
    int sz;
    cin >> sz;
    while (sz--) {
      int stop;
      double distance, time;
      cin >> stop >> distance >> time;
      wDist[i][stop] = distance;
      wTime[i][stop] = time;
    }
  }

	//We have now read in all the input. 
	//Now create an Adj list and matrix specifying the stops and addresses that are adjacent (within maximum walking distance)
	addrStopAdj.resize(addresses.size(), vector<bool>(stops.size(), false));
	addrAdjList.resize(addresses.size(), vector<int>());
	for (i = 0; i < addresses.size(); i++) {
		for (j = 1; j < stops.size(); j++) {
			if (wDist[i][j] <= maxWalkDist) {
				addrStopAdj[i][j] = true;
				addrAdjList[i].push_back(j);
			}
		}
		if (addrAdjList[i].size() == 0) {
			cerr << "Error. Address " << i << "(" << addresses[i].label << ") has no bus stop within " << maxWalkDist << " " << distUnits << ". Invalid input file\n";
			exit(1);
		}
		if (addrAdjList[i].size() == 1) {
			//Address adjacent to just one adjacent bus stop. So this stop is required in a solution
			stops[addrAdjList[i][0]].required = true;
		}
	}
	//Adj list specifying the addresses adjacent to each stop
	stopAdjList.resize(stops.size(), vector<int>());
	for (i = 1; i < stops.size(); i++) {
		for (j = 0; j < addresses.size(); j++) {
			if (wDist[j][i] <= maxWalkDist) stopAdjList[i].push_back(j);
		}
		if (stopAdjList[i].size() == 0) {
			cerr << "Error. Stop " << i << "(" << stops[i].label << ") is isolated (more than " << maxWalkDist << " " << distUnits <<" from any address). Invalid input file.\n";
			//If the following exit statement is removed, the program will work just fine. It is there to let me know if the problem instance has not been generated correctly
			exit(1);
		}
	}
	//In each adjacencey list we now sort the items so that, on each row i, the stops (addresses) are in ascending order of distance
	for (i = 0; i < addresses.size(); i++) {
		qSortStopsByDist(addrAdjList[i], 0, addrAdjList[i].size(), i);
	}
	for (i = 1; i < stops.size(); i++) {
		qSortAddressesByDist(stopAdjList[i], 0, stopAdjList[i].size(), i);
	}
  return cin;
}

void readInput(string &infile) {
	//Reads in the input file
	int i, j, x, y, numStops, numAddresses, numWalks;
	double d, t;
	string temp;

	totalPassengers = 0;

	ifstream inStream;
	inStream.open(infile);
	if (inStream.fail()) { cout << "ERROR OPENING INPUT FILE"; exit(1); }

	//First read the top line of the .bus file
	getline(inStream, temp, ',');
	numStops = stoi(temp);
	getline(inStream, temp, ',');
	numAddresses = stoi(temp);
	getline(inStream, temp, ',');
	numWalks = stoi(temp);
	getline(inStream, temp, ',');
	if (temp == "K") distUnits = "kms";
	else distUnits = "miles";
	getline(inStream, temp, ',');
	minEligibilityDist = stof(temp);
	getline(inStream, temp, ',');
	maxWalkDist = stof(temp);
	getline(inStream, temp, ',');
	trim(temp);
	//Read the rest of the line (doesn't do anything)
	getline(inStream, temp);

	cerr << "Processing " << infile << " " << temp << "\n";

	//Now resize the arrays
	stops.resize(numStops);
	addresses.resize(numAddresses);
	dTime.resize(numStops, vector<double>(numStops));
	dDist.resize(numStops, vector<double>(numStops));
	wTime.resize(numAddresses, vector<double>(numStops, DBL_MAX));
	wDist.resize(numAddresses, vector<double>(numStops, DBL_MAX));
	
	//Now read information about the stops
	for (i = 0; i < numStops; i++) {
		getline(inStream, temp, ',');
		getline(inStream, temp, ',');
		stops[i].y = stod(temp);
		getline(inStream, temp, ',');
		stops[i].x = stod(temp);
		getline(inStream, temp);
		trim(temp);
		stops[i].label = temp;
		stops[i].required = false;
	}

	//And similalrly for the addresses
	for (i = 0; i < numAddresses; i++) {
		getline(inStream, temp, ',');
		getline(inStream, temp, ','); 
		addresses[i].y = stod(temp);
		getline(inStream, temp, ',');
		addresses[i].x = stod(temp);
		getline(inStream, temp, ',');
		addresses[i].numPass = stoi(temp);
		totalPassengers += addresses[i].numPass;
		getline(inStream, temp);
		trim(temp);
		addresses[i].label = temp;
	}

	//Now read the distances between all stop pairs
	for (i = 0; i < numStops; i++) {
		for (j = 0; j < numStops; j++) {
			getline(inStream, temp, ',');
			getline(inStream, temp, ',');
			getline(inStream, temp, ',');
			getline(inStream, temp, ',');
			dDist[i][j] = stod(temp);
			getline(inStream, temp);
			dTime[i][j] = stod(temp);
		}
	}

	//Read information about a walk time distance pair
	for (i = 0; i < numWalks; i++) {
		getline(inStream, temp, ',');
		getline(inStream, temp, ',');
		x = stoi(temp);
		getline(inStream, temp, ',');
		y = stoi(temp);
		getline(inStream, temp, ',');
		d = stod(temp);
		getline(inStream, temp);
		t = stod(temp);
		wTime[x][y] = t;
		wDist[x][y] = d;
	}
	inStream.close();

	//We have now read in all the input. 
	//Now create an Adj list and matrix specifying the stops and addresses that are adjacent (within maximum walking distance)
	addrStopAdj.resize(addresses.size(), vector<bool>(stops.size(), false));
	addrAdjList.resize(addresses.size(), vector<int>());
	for (i = 0; i < addresses.size(); i++) {
		for (j = 1; j < stops.size(); j++) {
			if (wDist[i][j] <= maxWalkDist) {
				addrStopAdj[i][j] = true;
				addrAdjList[i].push_back(j);
			}
		}
		if (addrAdjList[i].size() == 0) {
			cout << "Error. Address " << i << "(" << addresses[i].label << ") has no bus stop within " << maxWalkDist << " " << distUnits << ". Invalid input file\n";
			exit(1);
		}
		if (addrAdjList[i].size() == 1) {
			//Address adjacent to just one adjacent bus stop. So this stop is required in a solution
			stops[addrAdjList[i][0]].required = true;
		}
	}
	//Adj list specifying the addresses adjacent to each stop
	stopAdjList.resize(stops.size(), vector<int>());
	for (i = 1; i < stops.size(); i++) {
		for (j = 0; j < addresses.size(); j++) {
			if (wDist[j][i] <= maxWalkDist) stopAdjList[i].push_back(j);
		}
		if (stopAdjList[i].size() == 0) {
			cout << "Error. Stop " << i << "(" << stops[i].label << ") is isolated (more than " << maxWalkDist << " " << distUnits <<" from any address). Invalid input file.\n";
			//If the following exit statement is removed, the program will work just fine. It is there to let me know if the problem instance has not been generated correctly
			exit(1);
		}
	}
	//In each adjacencey list we now sort the items so that, on each row i, the stops (addresses) are in ascending order of distance
	for (i = 0; i < addresses.size(); i++) {
		qSortStopsByDist(addrAdjList[i], 0, addrAdjList[i].size(), i);
	}
	for (i = 1; i < stops.size(); i++) {
		qSortAddressesByDist(stopAdjList[i], 0, stopAdjList[i].size(), i);
	}
}

extern vector<STOP> stops;
extern vector<ADDR> addresses;
extern vector<bool> isOutlier;
extern vector<vector<double> > dDist;
extern vector<vector<double> > dTime;
extern vector<vector<double> > wDist;
extern vector<vector<double> > wTime;
extern vector<vector<int> > stopAdjList;
extern vector<vector<int> > addrAdjList;
extern vector<vector<bool> > addrStopAdj;
extern int totalPassengers, maxBusCapacity, kInit;
extern double maxWalkDist;
extern double minEligibilityDist;
extern string distUnits;
extern double dwellPerPassenger;
extern double dwellPerStop;
extern double excessWeight;
extern double maxJourneyTime;
extern bool useMinCoverings;

inline
void swapVals(double &x, double &y) {
	double z; z = x; x = y; y = z;
}
inline
void swapVals(int &a, int &b) {
	int temp = a; a = b; b = temp;
}


void randPermute(vector<int> &A) {
	//Randomly permutes the contents of an array A
	if (A.empty()) return;
	int i, r;
	for (i = A.size() - 1; i >= 0; i--) {
		r = rand() % (i + 1);
		swap(A[i], A[r]);
	}
}

double sumDouble(vector<double> &X) {
	//Sums the numbers in X
	double total = 0;
	for (int i = 0; i < X.size(); i++) total += X[i];
	return total;
}

bool approxEqual(double x, double y) {
	//Checks if 2 doubles are equal to 5 dps
	if (abs(x - y) < 0.00001) return true;
	else return false;
}

double calcDwellTime(int numPass) {
	//Uses the length of a route l to calculate its cost
	return dwellPerStop + numPass * dwellPerPassenger;
}

double calcRCost(double l) {
	//Uses the length of a route l to calculate its cost
	if (l > maxJourneyTime) return maxJourneyTime + excessWeight * (l - maxJourneyTime + 1);
	else return l;
}

double calcRouteLenFromScratch(SOL &S, int route) {
	//Calculates the total time to traverse in a particular route using only items and W
	if (S.items[route].empty()) return 0.0;
	int i;
	double total = 0.0;
	for (i = 0; i < S.items[route].size() - 1; i++) {
		total += calcDwellTime(S.W[route][i]) + dTime[S.items[route][i]][S.items[route][i + 1]];
	}
	total += calcDwellTime(S.W[route][i]) + dTime[S.items[route][i]][0];
	return total;
}

double calcSolCostFromScratch(SOL &S) {
	int i;
	double tCst = 0, cst;
	for (i = 0; i < S.items.size(); i++) {
		cst = calcRCost(calcRouteLenFromScratch(S, i));
		tCst += cst;
	}
	return tCst;
}

bool containsOutlierStop(vector<int> &R) {
	//Returns true if route R contains an outlier stop
	for (int i = 0; i < R.size(); i++) {
		if (isOutlier[R[i]]) return true;
	}
	return false;
}

double calcWalkCostFromScratch(SOL &S) {
	//Takes a solution S and calculates its walkCost (each student walking to closest used stop)
	int i;
	double total = 0;
	for (i = 0; i < addresses.size(); i++) {
		total += addresses[i].numPass * wTime[i][S.assignedTo[i]];
	}
	return total;
}

int calcWSum(SOL &S, int v) {
	//Calculates the number of people boarding stop v according to S[W] only
	int i, r, c, total = 0;
	for (i = 0; i < S.routeOfStop[v].size(); i++) {
		r = S.routeOfStop[v][i];
		c = S.posInRoute[v][r];
		total += S.W[r][c];
	}
	return total;
}

double roundUp(double x, double base) {
	//Rounds x up to the nearest multiple of base
	if (base != 0 && x != 0) {
		double sign;
		if (x > 0) sign = 1;
		else sign = -1;
		x *= sign;
		x /= base;
		int fixedPoint = (int)ceil(x);
		x = fixedPoint * base;
		x *= sign;
	}
	return x;
}

double roundDown(double x, double base) {
	//Rounds x down to the nearest multiple of base
	if (base != 0 && x != 0) {
		double sign;
		if (x > 0) sign = 1;
		else sign = -1;
		x *= sign;
		x /= base;
		int fixedPoint = (int)floor(x);
		x = fixedPoint * base;
		x *= sign;
	}
	return x;
}

//-------------- Some procedures for checking and validating a solution --------------------------------
void prettyPrintSol(SOL &S) {
	int i, j;
	double tLen = 0, len, cst, tCst = 0;
	cout << "Rte    Act.-Len   Claim-len  Act-Cost  numPass\n";
	for (i = 0; i < S.items.size(); i++) {
		len = calcRouteLenFromScratch(S, i);
		cst = calcRCost(len);
		cout << setw(3) << i << setw(12) << len << setw(12) << S.routeLen[i] << setw(10) << cst << setw(9) << S.passInRoute[i] << "\t";
		if (S.items[i].empty()) cout << "-\n";
		else {
			cout << "{ ";
			for (j = 0; j < S.items[i].size() - 1; j++) cout << S.items[i][j] << " ";
			cout << S.items[i][j] << " }\n";
			tLen += len;
			tCst += cst;
		}
	}
	cout << "Actual Total Len = " << tLen << endl << "Actual Total Cost = " << tCst << endl << endl;
}

void checkCoveringIsMinimal(SOL &S, bool &OK) {
	//This checks the covering defined by stopUsed is minimal (i.e. that the removal of any stop causes
	//at least one address to not be served).
	//First, for each address count the number of adjacent stops in the solution and put this info in Y
	vector<int> Y(addresses.size(), 0);
	int i, j;
	for (i = 1; i < S.stopUsed.size(); i++) {
		if (S.stopUsed[i]) {
			for (j = 0; j < stopAdjList[i].size(); j++) Y[stopAdjList[i][j]] += 1;
		}
	}
	//Now, for each used stop, see if removing this stop causes an address to have no suitable stop; in which 
	//case the stop is definately needed. If it is not needed, then the matching is not minimal
	for (i = 1; i < S.stopUsed.size(); i++) {
		if (S.stopUsed[i]) {
			//Check if removing row i would give us an incomplete covering
			for (j = 0; j < stopAdjList[i].size(); j++) {
				if (Y[stopAdjList[i][j]] == 1) {
					break;
				}
			}
			if (j >= stopAdjList[i].size()) {
				cout << "Error: Stop " << i << " is not needed. Covering is not minimal.\n";
				OK = false;
			}
		}
	}
}

bool existsCommonStop(SOL &S, int r1, int r2) {
	//Returns true if routes r1 and r2 have a common stop, false otherwise
	int i, j;
	for (i = 0; i < S.items[r1].size(); i++) {
		for (j = 0; j < S.items[r2].size(); j++) {
			if (S.items[r1][i] == S.items[r2][j]) return true;
		}
	}
	return false;
}

bool contains(vector<int> &A, int x) {
	//Returns true iff x is an element in A
	for (int i = 0; i < A.size(); i++)
		if (A[i] == x) return true;
	return false;
}

void checkSolutionValidity(SOL &S, bool shouldBeMinimal) {
	//Performs a number of checks on a solution to see if it is valid and its cost values match those claimed.
	int i, j, n = stops.size(), m = addresses.size(), passInRoute = 0, totalNumPass = 0, numUsedStops = 0, solSize = 0;
	double timeToClosestStop;
	bool OK = true;
	vector<bool> used(n, false);
	//ID all stops used in the solution
	for (i = 0; i < S.items.size(); i++) {
		solSize += S.items[i].size();
		for (j = 0; j < S.items[i].size(); j++) {
			if (S.items[i][j] < 1 || S.items[i][j] >= n) {
				cout << "Error: Solution conains an invalid value (Route " << i << ", element " << j << +")\n";
				OK = false;
			}
			else {
				if (used[S.items[i][j]] == false) numUsedStops++;
				used[S.items[i][j]] = true;
			}
		}
	}
	//Check that the claimed values for S.solSize and S.numUsedStops are correct
	if (S.solSize != solSize) {
		cout << "Error: S.solSize (" << S.solSize << ") and actual number (" << solSize << ") do not match\n";
		OK = false;
	}
	if (S.numUsedStops != numUsedStops) {
		cout << "Error: S.numUsedStops (" << S.numUsedStops << ") and actual number (" << numUsedStops << ") do not match\n";
		OK = false;
	}
	//Check for existence of duplicates in each route.
	vector<int> appearsInRoute(n, 0);
	for (i = 0;i < S.items.size(); i++) {
		for (j = 0; j < S.items[i].size(); j++) appearsInRoute[S.items[i][j]]++;
		for (j = 0; j < S.items[i].size(); j++) if (appearsInRoute[S.items[i][j]] > 1) {
			cout << "Error: Route " << i << " contains a duplicate stop (" << S.items[i][j] << ")\n";
			OK = false;
		}
		for (j = 0; j < S.items[i].size(); j++) appearsInRoute[S.items[i][j]] = 0;
	}
	//Check the validity of the routeOfStop array (both ways)
	for (i = 0; i < S.items.size(); i++) {
		for (j = 0; j < S.items[i].size(); j++) {
			if (!contains(S.routeOfStop[S.items[i][j]], i)) {
				cout << "Error: S.routeOfStop and S.items are inconsistent (a) for (stop " << S.items[i][j] << ")\n";
				OK = false;
			}
		}
	}
	for (i = 0; i < S.routeOfStop.size(); i++) {
		for (j = 0; j < S.routeOfStop[i].size(); j++) {
			if (!contains(S.items[S.routeOfStop[i][j]], i)) {
				cout << "Error: S.routeOfStop and S.items are inconsistent (b) for (stop " << i << ")\n";
				OK = false;
			}
		}
	}
	//Also check the validity of the commonStops matrix
	if (S.items.size() > 1) {
		for (i = 0; i < S.commonStop.size() - 1; i++) {
			for (j = i + 1; j < S.commonStop[i].size(); j++) {
				if (S.commonStop[i][j] != S.commonStop[j][i]) {
					cout << "Error: S.commonStop is not symmetric\n";
					OK = false;
				}
				else if (S.commonStop[i][j] != existsCommonStop(S, i, j)) {
					cout << "Error S.commonStop and solution are inconsistent\n";
					OK = false;
				}
			}
		}
	}
	//And check the validity of the S.posInRoute matrix
	for (i = 0; i < S.posInRoute.size(); i++) {
		for (j = 0; j < S.posInRoute[i].size(); j++) {
			if (S.posInRoute[i][j] != -1) {
				if (S.posInRoute[i][j] >= S.items[j].size()) {
					cout << "Error S.posInRoute is not consistent with S.items\n";
					OK = false;
				}
				else if ( S.items[j][S.posInRoute[i][j]] != i) {
					cout << "Error S.posInRoute is not consistent with S.items\n";
					OK = false;
				}
			}
		}
	}
	for (i = 0; i < S.items.size(); i++) {
		for (j = 0; j < S.items[i].size(); j++) {
			if (S.posInRoute[S.items[i][j]][i] != j) {
				cout << "Error S.posInRoute is not consistent with S.items\n";
				OK = false;
			}
		}
	}
	//Check that the correct routes contain the outliers (if there are any at all)
	int outlierRouteCnt = 0;
	for (i = 0; i < S.items.size(); i++) {
		if (containsOutlierStop(S.items[i]) == true) {
			outlierRouteCnt++;
			if (S.hasOutlier[i] == false) {
				cout << "Error: Route " << i << " is claimed to have an outlier stop, but doesn't\n";
				OK = false;
			}
		}
		else {
			if (S.hasOutlier[i] == true) {
				cout << "Error: Route " << i << " is claimed to not have an outlier stop, but it does\n";
				OK = false;
			}
		}
	}
	if (S.numRoutesWithOutliers != outlierRouteCnt) cout << "Error. Claimed value for S.numRoutesWithOutliers (" << S.numRoutesWithOutliers << ") not correct. It should be " << outlierRouteCnt << "\n";
	//Check that the S.items and S.W arrays match
	if (S.items.size() != S.W.size()) {
		cout << "Error: S.items and S.W contain different number of routes.\n";
		OK = false;
	}
	else {
		for (i = 0; i < S.items.size(); i++) {
			if (S.items[i].size() != S.W[i].size()) {
				cout << "Error: Rows " << i << " in S.items and S.W are different in size and therefore invalid.\n";
				OK = false;
			}
		}
	}
	//Check that S.W holds valid values
	for (i = 0; i < S.W.size(); i++) {
		for (j = 0; j < S.W[i].size(); j++) {
			if (S.W[i][j] < 0) {
				cout << "Error: S.W " << i << "," << j << " has value " << S.W[i][j] << ". Only +ve integers allowed (zero is also allowed when using EmptyX operator)\n";
				OK = false;
			}
		}
	}
	//Check validity of S.stopUsed
	for (i = 1; i < n; i++) {
		if (S.stopUsed[i] && !used[i]) {
			cout << "Error: Stop " << i << " is recorded as being used in the stopUsed array, but is not actually used\n";
			OK = false;
		}
		else if (!S.stopUsed[i] && used[i]) {
			cout << "Error: Stop " << i << " is being used in the solution, but the stopUsed array does not record this\n";
			OK = false;
		}
	}
	//If specified, check that S.stopUsed defines a minimal covering
	if (shouldBeMinimal && useMinCoverings) checkCoveringIsMinimal(S, OK);
	//Check that the number of recorded empty stops is correct
	int emptyCount = 0;
	for (i = 0; i < S.items.size(); i++) if (S.items[i].empty()) emptyCount++;
	if (emptyCount != S.numEmptyRoutes) {
		cout << "Error: There are " << emptyCount << " empty routes, but S records this as " << S.numEmptyRoutes << "\n";
		OK = false;
	}
	//Check that each address i is assigned to the closest used stop
	for (i = 0; i < m; i++) {
		timeToClosestStop = DBL_MAX;
		//Recall that the addrAdjList structure has, for each address, the adjacent stops in non-descending order of time
		for (j = 0; j < addrAdjList[i].size(); j++) {
			if (used[addrAdjList[i][j]]) {
				timeToClosestStop = wTime[i][addrAdjList[i][j]];
				break;
			}
		}
		if (j >= addrAdjList[i].size() || timeToClosestStop == DBL_MAX) {
			cout << "Error: Address " << i << " does not have a used stop within " << maxWalkDist << distUnits << "\n";
			OK = false;
		}
		else if (addrAdjList[i][j] != S.assignedTo[i] && wTime[i][S.assignedTo[i]] != timeToClosestStop) {
			cout << "Error: Address " << i << " is assigned to stop " << S.assignedTo[i] << " in the solution (" << wTime[i][S.assignedTo[i]] << "), while the closest available stop is " << addrAdjList[i][j] << "(" << timeToClosestStop << ")\n";
			OK = false;
		}
	}
	//Check that the number of students boarding at each stop is valid and adds up to the correct amount
	for (i = 0; i < S.W.size(); i++) {
		passInRoute = 0;
		for (j = 0; j < S.W[i].size(); j++) {
			passInRoute += S.W[i][j];
			totalNumPass += S.W[i][j];
		}
		if (passInRoute != S.passInRoute[i]) {
			cout << "Error: Route " << i << " S.passInRoute value does not match the number calculated manually\n";
			OK = false;
		}
		if (passInRoute > maxBusCapacity) {
			cout << "Error: Route " << i << " contains " << passInRoute << " passengers, which is more than the allowed maximum of " << maxBusCapacity << "\n";
			OK = false;
		}
	}
	if (totalNumPass != totalPassengers) {
		cout << "Error: Total passengers in S.W (" << totalNumPass << ") does not equal actual total number of passengers (" << totalPassengers << ")\n";
		OK = false;
	}
	//Check that all passengers are served in S
	vector<int> numAtStop(n, 0);
	for (i = 0; i < S.W.size(); i++) {
		for (j = 0; j < S.W[i].size(); j++) {
			numAtStop[S.items[i][j]] += S.W[i][j];
		}
	}
	for (i = 0; i < n; i++) {
		if (numAtStop[i] != S.numBoarding[i]) {
			cout << "Error: Total number of people recorded as using stop " << i << " in S.W " << numAtStop[i] << " not equal to number specified in S.numBoarding (" << S.numBoarding[i] << ")\n";
			OK = false;
		}
	}
	for (i = 1; i < n; i++) {
		if (S.numBoarding[i] < 0) {
			cout << "Error: Number recorded as boarding at stop " << i << " in S.numBoarding is invalid (" << S.numBoarding[i] << ")\n";
			OK = false;
		}
		if (S.numBoarding[i] == 0 && S.stopUsed[i]) {
			cout << "Error: No students boarding at stop " << i << ", but it is still being used in the solution.\n";
			OK = false;
		}
		if (S.numBoarding[i] > 0 && !S.stopUsed[i]) {
			cout << "Error: " << S.numBoarding[i] << " students boarding at stop " << i << ", but it is not recorded as being used in the solution.\n";
			OK = false;
		}
	}
	//Check that the claimed route lengths are correct
	double actualCost = 0.0, actualRouteLen;
	for (i = 0; i < S.items.size(); i++) {
		actualRouteLen = calcRouteLenFromScratch(S, i);
		actualCost += calcRCost(actualRouteLen);
		if (!approxEqual(S.routeLen[i], actualRouteLen)) {
			cout << "Error: Claimed length of Route " << i << " (" << S.routeLen[i] << ") does not match actual cost of " << calcRouteLenFromScratch(S, i) << "\n";
			OK = false;
		}
	}
	//NOTE: We check the S.cost variable directly here, but in reality there may be a discrpancy if the weight has changed
	if (!approxEqual(S.cost, actualCost)) {
		cout << "Error: Claimed cost of solution (" << S.cost << ") does not match actual cost of " << actualCost << "\n";
		OK = false;
	}
	double actualWalkCost = calcWalkCostFromScratch(S);
	if (!approxEqual(S.costWalk, actualWalkCost)) {
		cout << "Error: Claimed Walking cost of solution (" << S.costWalk << ") does not match actual cost of " << actualWalkCost << "\n";
		OK = false;
	}
	//If there is an error, report it and exit
	if (!OK) {
		prettyPrintSol(S);
		exit(1);
	}
}

//-------------- Some procedures for adding solutions to the slnSet (if apt) --------------------------------
void reduceNumBuses(SOL &S, int busesRequired) {
	//Removes empty buses from a solution until we have the required number
	int i = 0, j;
	while (i < S.items.size()) {
		if (S.items[i].empty()) {
			//Delete all information relating to this route
			S.items.erase(S.items.begin() + i);
			S.W.erase(S.W.begin() + i);
			S.routeLen.erase(S.routeLen.begin() + i);
			S.passInRoute.erase(S.passInRoute.begin() + i);
			S.hasOutlier.erase(S.hasOutlier.begin() + i);
			S.numEmptyRoutes--;
			S.numFeasibleRoutes--;
			for (int r = 0; r < S.posInRoute.size(); r++) {
				S.posInRoute[r].erase(S.posInRoute[r].begin() + i);
			}
			for (int r = 0; r < S.commonStop.size(); r++) {
				S.commonStop[r].erase(S.commonStop[r].begin() + i);
			}
			S.commonStop.erase(S.commonStop.begin() + i);
		}
		else i++;
		if (S.items.size() == busesRequired) break;
	}
	//Remember to update the routeOfBus array
	for (i = 0; i < S.routeOfStop.size(); i++) S.routeOfStop[i].clear();
	for (i = 0; i < S.items.size(); i++) for (j = 0; j < S.items[i].size(); j++) S.routeOfStop[S.items[i][j]].push_back(i);
}

void addEmptyRoute(SOL &S) {
	//Adds a single empty route to the solution S and updates all data structures
	int i, k = S.items.size();
	for (i = 0; i < k; i++) S.commonStop[i].push_back(false);
	S.commonStop.push_back(vector<bool>(k, false));
	for (i = 1; i < stops.size(); i++) S.posInRoute[i].push_back(-1);
	S.items.push_back(vector<int>());
	S.W.push_back(vector<int>());
	S.routeLen.push_back(0.0);
	S.passInRoute.push_back(0);
	S.hasOutlier.push_back(false);
	S.numEmptyRoutes++;
	S.numFeasibleRoutes++;
}

//--------------Some functions for calculating metrics for output----------------------------------------/
void calcMetrics(double &stopsPerAddr, double &addrPerStop) {
	//Calculate some metrics for output: First calculate numAddresses per stop and num stops per address
	int i, total1 = 0, total2 = 0;
	stopsPerAddr = addrPerStop = 0.0;
	for (i = 1; i < stopAdjList.size(); i++) total1 += stopAdjList[i].size();
	for (i = 0; i < addrAdjList.size(); i++) total2 += addrAdjList[i].size();
	addrPerStop = total1 / double(stopAdjList.size() - 1);
	stopsPerAddr = total2 / double(addrAdjList.size());
}

int calcSingletonStops(SOL &S) {
	//Calculate the number of stops that are used just once
	int i, numSingletonStops = 0;
	for (i = 1; i < stops.size(); i++) {
		if (S.routeOfStop[i].size() == 1) numSingletonStops++;
	}
	return numSingletonStops;
}

void getOutliers() {
	//Determines any stops that are compulsory and that are too far from the school 
	int i, j, stus;
	bool containsOutlier = false;
	isOutlier.resize(stops.size(), false);
	for (i = 1; i < stops.size(); i++) {
		if (dTime[i][0] > maxJourneyTime) {
			isOutlier[i] = true;
			cout << "Bus Stop " << i << " = \"" << stops[i].label << "\" is an outlier (" << ceil(dTime[i][0] / 60.0) << " mins from the school)\n";
			containsOutlier = true;
		}
		else if (stops[i].required) {
			//Calculate the smallest number of students who will be boarding stop i if it is being used (i.e. the num stus for whom i is their closest stop)
			stus = 0;
			for (j = 0; j < addrAdjList.size(); j++) {
				if (addrAdjList[j][0] == i) stus += addresses[j].numPass;
			}
			//and also check if this makes the stop an outlier
			if (dTime[i][0] + calcDwellTime(stus) > maxJourneyTime) {
				isOutlier[i] = true;
				cout << "Bus Stop " << i << " = \"" << stops[i].label << "\" is an outlier (" << ceil(dTime[i][0] / 60.0) << " mins from the school, plus at least " << stus << " students must board here)\n";
				containsOutlier = true;
			}
		}
	}
	if(containsOutlier) cout << "Routes containing outlier bus stops do not need to have lengths less than m_t to be feasible.\n\n";
}

extern vector<STOP> stops;
extern vector<ADDR> addresses;
extern vector<bool> isOutlier;
extern vector<vector<double> > dDist;
extern vector<vector<double> > dTime;
extern vector<vector<double> > wDist;
extern vector<vector<double> > wTime;
extern vector<vector<int> > stopAdjList;
extern vector<vector<int> > addrAdjList;
extern vector<vector<bool> > addrStopAdj;
extern int totalPassengers, maxBusCapacity;
extern double maxWalkDist;
extern double minEligibilityDist;
extern string distUnits;
extern double dwellPerPassenger;
extern double dwellPerStop;
extern double excessWeight;
extern double maxJourneyTime;

void quickRemove(int pos, vector<int> &itemWeight, vector<int> &itemLabel) {
	swapVals(itemWeight[pos], itemWeight.back());
	swapVals(itemLabel[pos], itemLabel.back());
	itemWeight.pop_back();
	itemLabel.pop_back();
}

int getLargestItem(vector<int> &itemWeight) {
	//Returns the position of the largest integer in a vector of integers
	int i, max = itemWeight[0], maxPos = 0;
	for (i = 1; i < itemWeight.size(); i++) {
		if (itemWeight[i] > max) {
			max = itemWeight[i];
			maxPos = i;
		}
	}
	return maxPos;
}

int posOfItemInBin(int item, vector<int> &items) {
	//Tells us the position of "item" in an array. Returns -1 if it isn't present
	int i;
	for (i = 0; i < items.size(); i++) {
		if (items[i] == item) return i;
	}
	return -1;
}

int chooseBinWithEnoughCapacity(vector<int> &binWeight, vector<vector<int> > &items, int v, int weightv, int &posOfV) {
	//Find the most suitable bin for item v. Do this by returning the first bin that has with adequate capacity 
	//and that already contains v. If such a bin does not exist, return the first bin with adequate capacity that 
	//does not contain v. Return -1 if neither exists.
	int i, k = binWeight.size(), binNoMultiStop = -1, pos;
	for (i = 0; i < k; i++) {
		if (binWeight[i] + weightv <= maxBusCapacity) {
			pos = posOfItemInBin(v, items[i]);
			if (pos != -1) {
				posOfV = pos;
				return i;
			}
			else if (binNoMultiStop == -1) {
				binNoMultiStop = i;
			}
		}
	}
	posOfV = -1;
	return binNoMultiStop;
}

int chooseEmptiestBin(vector<int> &binWeight, vector<vector<int> > &items, int v, int weightv, int &posOfV) {
	//This is used when no bin has adequate capacity. We therefore choose the emptiest bin that already contains v.
	//If none exists, just choose the emptiest bin. Assumes all bin weights are <= maxBusCapacity
	int i, k = binWeight.size(), minMulti = maxBusCapacity, minNoMulti = maxBusCapacity, minMultiPos = -1, minNoMultiPos = -1, pos;
	for (i = 0; i < k; i++) {
		pos = posOfItemInBin(v, items[i]);
		if (pos != -1) {
			if (binWeight[i] < minMulti) {
				minMulti = binWeight[i];
				posOfV = pos;
				minMultiPos = i;
			}
		}
		else {
			if (binWeight[i] < minNoMulti) {
				minNoMulti = binWeight[i];
				minNoMultiPos = i;
			}
		}
	}
	if (minMultiPos != -1) {
		return minMultiPos;
	}
	else {
		posOfV = -1;
		return minNoMultiPos;
	}
}

void binPacker(vector<vector<int> > &items, vector<vector<int> > &W, vector<int> &binSize, vector<int> &itemsToAdd, vector<int> &itemsToAddWeight) {
	//Generates an assignment of stops to buses / routes using BPP heuristics
	int pos, bin, spare, j;
	//Call the FFD-style BPP algorithm
	while (!itemsToAdd.empty()) {
		//Identify the largest item and search for a suitable bin
		pos = getLargestItem(itemsToAddWeight);
		bin = chooseBinWithEnoughCapacity(binSize, items, itemsToAdd[pos], itemsToAddWeight[pos], j);
		if (bin != -1) {
			//Bin with adequate capacity found. Assign item to bin and remove it from the itemWeight and itemLabel list.
			//If the item is already in the bin (j != -1), merge them, else just add it to the end
			if (j == -1) {
				items[bin].push_back(itemsToAdd[pos]);
				W[bin].push_back(itemsToAddWeight[pos]);
			}
			else {
				W[bin][j] += itemsToAddWeight[pos];
			}
			binSize[bin] += itemsToAddWeight[pos];
			quickRemove(pos, itemsToAddWeight, itemsToAdd);
		}
		else {
			//No single bin can accommodate the item, so use the bin with the most spare capacity for some of it
			//Again, if the item is already in the bin, merge them, else just add it to the end
			bin = chooseEmptiestBin(binSize, items, itemsToAdd[pos], itemsToAddWeight[pos], j);
			spare = maxBusCapacity - binSize[bin];
			if (j == -1) {
				items[bin].push_back(itemsToAdd[pos]);
				W[bin].push_back(spare);
			}
			else {
				W[bin][j] += spare;
			}
			binSize[bin] += spare;
			itemsToAddWeight[pos] -= spare;
		}
	}
}

void binPacker(vector<vector<int> > &items, vector<vector<int> > &W, vector<int> &binSize, int itemToPack, int itemToPackSize) {
	//Overloaded version of the above that packs just one item (bus stop)
	int bin, spare, j;
	while (true) {
		//Find a suitable bin
		bin = chooseBinWithEnoughCapacity(binSize, items, itemToPack, itemToPackSize, j);
		if (bin != -1) {
			//Assign item to bin i. (If the item is already in bin i, merge them)
			if (j == -1) {
				items[bin].push_back(itemToPack);
				W[bin].push_back(itemToPackSize);
			}
			else {
				W[bin][j] += itemToPackSize;
			}
			binSize[bin] += itemToPackSize;
			return;
		}
		else {
			//No single bin can accommodate the item, so use the bin with the most spare capacity for some of it
			bin = chooseEmptiestBin(binSize, items, itemToPack, itemToPackSize, j);
			spare = maxBusCapacity - binSize[bin];
			j = posOfItemInBin(itemToPack, items[bin]);
			if (j == -1) {
				items[bin].push_back(itemToPack);
				W[bin].push_back(spare);
			}
			else {
				W[bin][j] += spare;
			}
			binSize[bin] += spare;
			itemToPackSize -= spare;
		}
	}
}


extern vector<STOP> stops;
extern vector<ADDR> addresses;
extern vector<bool> isOutlier;
extern vector<vector<double> > dDist;
extern vector<vector<double> > dTime;
extern vector<vector<double> > wDist;
extern vector<vector<double> > wTime;
extern vector<vector<int> > stopAdjList;
extern vector<vector<int> > addrAdjList;
extern vector<vector<bool> > addrStopAdj;
extern int totalPassengers, maxBusCapacity;
extern double maxWalkDist;
extern double minEligibilityDist;
extern string BingKey;
extern string distUnits;
extern double dwellPerPassenger;
extern double dwellPerStop;
extern double excessWeight;
extern double maxJourneyTime;
extern bool useMinCoverings;

//Some temporary vectors used in the covering functions
vector<int> Y, tempVec, perm;
vector<vector<int> > X;

int chooseRandomSet(vector<vector<int> > &X) {
	//Chooses any set with an element to cover, breaking ties randomly
	int i, pos = -1, numChoices = 0;
	for (i = 1; i < X.size(); i++) {
		if (X[i].size() > 0) {
			if (rand() % (numChoices + 1) == 0) {
				pos = i;
			}
			numChoices++;
		}
	}
	if (pos == -1) { cout << "Error in chooseRandomSet function. Ending...\n"; exit(1); }
	else return pos;
}

int chooseBiggestSet(vector<vector<int> > &X) {
	//Chooses the biggest set (stop with the most unvisited addresses), breaking ties randomly
	int i, max = 0, maxPos = -1, numChoices = 0;
	for (i = 1; i < X.size(); i++) {
		if (X[i].size() >= max) {
			if (X[i].size() > max) numChoices = 0;
			if (rand() % (numChoices + 1) == 0) {
				max = X[i].size();
				maxPos = i;
			}
			numChoices++;
		}
	}
	if (maxPos == -1) { cout << "Error in chooseBiggestSet function. Ending...\n"; exit(1); }
	else return maxPos;
}

void getClosestStops(vector<bool> &stopUsed) {
	//Creates a covering by simply taking the closest stop to each address
	int i;
	for (i = 0; i < addresses.size(); i++) {
		stopUsed[addrAdjList[i][0]] = true;
	}
}

void makeCoveringMinimal(vector<bool> &stopUsed) {
	//This checks the covering is minimal. If it is not, bus stops are removed in a random order to make it minimal. 
	int i, j, r, stop;
	tempVec.clear();
	Y.clear();
	Y.resize(addresses.size(), 0);
	//Make a list of all stops being used
	for (i = 1; i < stopUsed.size(); i++) {
		if (stopUsed[i]) tempVec.push_back(i);
	}
	//First, for each address count the number of adjacent stops in the solution and put this info in Y
	for (i = 0; i < tempVec.size(); i++) {
		stop = tempVec[i];
		for (j = 0; j < stopAdjList[stop].size(); j++) Y[stopAdjList[stop][j]] += 1;
	}
	//Now, for each used stop in a random order, see if removing this stop causes an address to have no suitable stop; in which 
	//case the stop is definately needed. If it is not needed, then it is removed
	randPermute(tempVec);
	for (i = 0; i < tempVec.size(); i++) {
		stop = tempVec[i];
		//Check if removing "stop" would give us an incomplete covering
		for (j = 0; j < stopAdjList[stop].size(); j++) {
			if (Y[stopAdjList[stop][j]] == 1) break;
		}
		if (j >= stopAdjList[stop].size()) {
			//If we are here then "stop" can be removed from the solution 
			for (r = 0; r < stopAdjList[stop].size(); r++) Y[stopAdjList[stop][r]]--;
			stopUsed[stop] = false;
		}
	}
}

void generateNewCovering(vector<bool> &stopUsed, int forbidden, int heuristic) {
	//Executes a greedy set covering algorithm to determine a subset of bus stops to use.
	//Uses the global variable "makeCoveringMinimal" to determine whether the set of bus stops should correspond to a minimal covering (invoking a procedure at the end)
	//"Forbidden" defines a single stop that should not be included in this covering (if it is -1 then all are allowed)
	//Heuristic: 1: choose set with most uncovered elements at each iteration
	//           2: choose any set with an uncovered element at each iteration
	int i, j, x, cnt = 0;
	X.clear();
	X.resize(stops.size());
	tempVec.clear();

	//Set up a multiset of sets X, each set is the adjacencies of a stop (in lexicographic order)	
	for (i = 1; i < stops.size(); i++) {
		for (j = 0; j < addresses.size(); j++) {
			if (addrStopAdj[j][i]) X[i].push_back(j);
		}
	}

	//This is optional and stops a particular stop from being selected as part of the covering
	if (forbidden >= 0 && forbidden < X.size()) {
		X[forbidden].clear();
	}

	//Now, if the stopUsed contains any true values, add these to the covering (they are already conributing to the covering)
	for(x = 1; x < stops.size(); x++) {
		if (stopUsed[x] == true) {
			cnt += X[x].size();
			//Remove the items in X[x] from all other sets X[i]
			for (i = 1; i < X.size(); i++) {
				if (i != x) {
					//Remove elements of X[x] from X[i] (i.e. Calculate (X[i] setminus X[x]) and put the results back into X[i])
					tempVec.clear();
					set_difference(X[i].begin(), X[i].end(), X[x].begin(), X[x].end(), back_inserter(tempVec));
					X[i].swap(tempVec);
				}
			}
			X[x].clear();
		}
	}

	if (cnt < addresses.size()) {
		//If we are here, the covering is incomplete, so we repeatedly select sets (bus stops) until we have a complete covering
		while (true) {
			if (heuristic == 1) {
				x = chooseBiggestSet(X);
			}
			else {
				x = chooseRandomSet(X);
			}
			cnt += X[x].size();
			stopUsed[x] = true;
			//Remove the items in X[x] from all other sets X[i]
			for (i = 1; i < X.size(); i++) {
				if (i != x) {
					tempVec.clear();
					set_difference(X[i].begin(), X[i].end(), X[x].begin(), X[x].end(), back_inserter(tempVec));
					X[i].swap(tempVec);
				}
			}
			X[x].clear();
			if (cnt >= addresses.size()) break;
		}
	}

	//If necesarry, now ensure that this covering is minimal
	if (useMinCoverings) {
		makeCoveringMinimal(stopUsed);
	}
}
vector<int> stopsToPack, weightOfStopsToPack;

void eliminateFromW(SOL &S, int v, int x) {
	//Eliminates x passengers from occurrences of stop v in S.W and updates S.passInRoute
	int i, r, c;
	for (i = 0; i < S.routeOfStop[v].size(); i++) {
		r = S.routeOfStop[v][i];
		c = S.posInRoute[v][r];
		if (x <= S.W[r][c]) {
			S.passInRoute[r] -= x;
			S.W[r][c] -= x;
			return;
		}
		else {
			S.passInRoute[r] -= S.W[r][c];
			x -= S.W[r][c];
			S.W[r][c] = 0;
		}
	}
	cout << "Error: should not be here at all....\n";
	exit(1);
}

void repopulateAuxiliaries(SOL &S) {
	//This procedure takes a solution defined according to the following structures
	//S.stopUsed, S.assignedTo, S.numBoarding, S.W, S.items, and S.passInRoute.
	//It then uses these to repopulate the remaining auxiliary structures (not the costs though)	
	int i, j, u, k = S.items.size();
	S.routeOfStop.clear();
	S.routeOfStop.resize(stops.size(), vector<int>());
	S.stopUsed.clear();
	S.stopUsed.resize(stops.size(), false);
	S.routeLen.clear();
	S.routeLen.resize(k, 0.0);
	S.hasOutlier.clear();
	S.hasOutlier.resize(k, false);
	S.posInRoute.clear();
	S.posInRoute.resize(stops.size(), vector<int>(k, -1));
	S.commonStop.clear();
	S.commonStop.resize(k, vector<bool>(k, false));
	S.numFeasibleRoutes = 0;
	S.numEmptyRoutes = k;
	S.numUsedStops = 0;
	S.solSize = 0;
	S.numRoutesWithOutliers = 0;
	for (i = 0; i < S.items.size(); i++) {
		//Calculate solSize and numEmptyRoutes
		S.solSize += S.items[i].size();
		for (j = 0; j < S.items[i].size(); j++) {
			u = S.items[i][j];
			//Calculate stopUsed array
			if (S.stopUsed[u] == false) {
				S.stopUsed[u] = true;
				S.numUsedStops++;
			}
			//Calculate stuff to do with outliers
			if (isOutlier[u]) S.hasOutlier[i] = true;
			//Calculate pos in route
			S.posInRoute[u][i] = j;
			S.routeOfStop[u].push_back(i);
		}
	}
	//Now populate the commonStop matrix (assuming there is more than one route)
	if (k > 1) {
		for (i = 0; i < k - 1; i++) {
			for (j = i + 1; j < k; j++) {
				if (existsCommonStop(S, i, j)) {
					S.commonStop[i][j] = true;
					S.commonStop[j][i] = true;
				}
			}
		}
	}
	//Next calculate the raw length of each route (no weightings -- just travel and dwell times) and the num routes containing outliers
	for (i = 0; i < k; i++) {
		S.routeLen[i] = calcRouteLenFromScratch(S, i);
		if (!S.items[i].empty()) S.numEmptyRoutes--;
		if (S.hasOutlier[i]) S.numRoutesWithOutliers++;
		if (S.routeLen[i] <= maxJourneyTime || S.hasOutlier[i]) S.numFeasibleRoutes++;
	}
}

void rebuildSolution(SOL &S) {
	//Takes an existing solution and a new minimal covering of bus stops and adapts the solution accordingly 
	int i, j, r, c, v, x, k = S.items.size(), excess;
	//First assign each address to the closest used bus stop
	for (i = 0; i < addresses.size(); i++) {
		for (j = 0; j < addrAdjList[i].size(); j++) {
			if (S.stopUsed[addrAdjList[i][j]]) {
				S.assignedTo[i] = addrAdjList[i][j];
				break;
			}
		}
	}
	//And calculate the number boarding at each stop
	S.numBoarding.clear();
	S.numBoarding.resize(stops.size(), 0);
	for (i = 0; i < addresses.size(); i++) {
		for (j = 0; j < addrAdjList[i].size(); j++) {
			if (S.stopUsed[addrAdjList[i][j]]) {
				S.numBoarding[addrAdjList[i][j]] += addresses[i].numPass;
				break;
			}
		}
	}
	//If there are any stops with no students assigned to them, delete them from the solution
	for (i = 1; i < stops.size(); i++) {
		if (S.numBoarding[i] <= 0) {
			S.stopUsed[i] = false;
		}
	}
	//Now set up the bin packing problem by altering S.W and S.passInRoute, and building up BPP arrays
	stopsToPack.clear();
	weightOfStopsToPack.clear();
	for (v = 1; v < stops.size(); v++) {
		if (S.stopUsed[v]) {
			//Calculate number boarding stop v in the old solution (i.e. according to S.W)
			x = calcWSum(S, v);
			if (x < S.numBoarding[v]) {
				//A further (S.numBoarding[v] - x) passengers boarding at v need to packed into the solution
				stopsToPack.push_back(v);
				weightOfStopsToPack.push_back(S.numBoarding[v] - x);
			}
			else if (x > S.numBoarding[v]) {
				//some excess passengers need to be removed from instances of v in S.W (too many currently boarding v)
				excess = x - S.numBoarding[v];
				eliminateFromW(S, v, excess);
			}
		}
		else {
			//Stop v is not being used now, so set all related S[W]'s to zero and update passInRoute
			for (i = 0; i < S.routeOfStop[v].size(); i++) {
				r = S.routeOfStop[v][i];
				c = S.posInRoute[v][r];
				S.passInRoute[r] -= S.W[r][c];
				S.W[r][c] = 0;
			}
		}
	}
	//Now remove any stops in the solution for which S.W[i][j] = 0;
	for (i = 0; i < k; i++) {
		j = 0;
		while (j < S.W[i].size()) {
			if (S.W[i][j] == 0) {
				S.W[i].erase(S.W[i].begin() + j);
				S.items[i].erase(S.items[i].begin() + j);
			}
			else j++;
		}
	}
	//We can now pack the remaining stops into the solution 
	binPacker(S.items, S.W, S.passInRoute, stopsToPack, weightOfStopsToPack);

	//Finally, we need to repopulate the residual structures. 
	repopulateAuxiliaries(S);
	
	//...and calculate the costs
	S.cost = calcSolCostFromScratch(S);
	S.costWalk = calcWalkCostFromScratch(S);
}


int makeNewCovering(SOL &S) {
	//Delete some (non-required) stops and then repair via the set covering method
	int i;
	
	//Create a random permutation of the used stops that are not "required"
	tempVec.clear();
	for (i = 1; i < S.stopUsed.size(); i++) {
		if (S.stopUsed[i] == true && !stops[i].required) tempVec.push_back(i);
	}
	randPermute(tempVec);

	//If all stops are required, then end (we can't change the solution)
	if (tempVec.empty()) {
		return 0;
	}

	//This is the probability of removing a non-essential stop
	double p = 3 / double(tempVec.size());

	//Select the stops to delete. One stop is removed automatically, the rest according to binomial probabilities
	perm.clear();
	perm.push_back(tempVec[0]);
	for (i = 1; i < tempVec.size(); i++) {
		if (rand() / double(RAND_MAX) <= p) perm.push_back(tempVec[i]);
	}

	//Now delete these stops from the stopUsed array and find a new minimal covering. We forbid the first stop in
	//tempVec2 from being reselected to ensure the new set cover is different
	for (i = 0; i < perm.size(); i++) S.stopUsed[perm[i]] = false;
	generateNewCovering(S.stopUsed, perm[0], 2);

	//And finally rebuild the solution according to the new (minimal set of bus stops)
	rebuildSolution(S);
	return perm.size();
}

extern vector<STOP> stops;
extern vector<ADDR> addresses;
extern vector<bool> isOutlier;
extern vector<vector<double> > dDist;
extern vector<vector<double> > dTime;
extern vector<vector<double> > wDist;
extern vector<vector<double> > wTime;
extern vector<vector<int> > stopAdjList;
extern vector<vector<int> > addrAdjList;
extern vector<vector<bool> > addrStopAdj;
extern int totalPassengers, maxBusCapacity;
extern double maxWalkDist;
extern double minEligibilityDist;
extern string distUnits;
extern double dwellPerPassenger;
extern double dwellPerStop;
extern double excessWeight;
extern double maxJourneyTime;


void makeInitSol(SOL &S, int k, int heuristic) {
	//For the set covering algorithm a greedy algorithm is used. 
	//Heuristic: 1: choose set with most uncovered elements at each iteration
	//           2: choose any set with an uncovered element at each iteration
	//			 3: This is different, it simply takes the stops closest to each student	
	int i, j;
	
	//Initialise the arrays that define the solution 
	S.items = vector<vector<int> >(k, vector<int>());
	S.W = vector<vector<int> >(k, vector<int>());
	S.stopUsed = vector<bool>(stops.size(), false);
	S.assignedTo = vector<int>(addresses.size());
	S.numBoarding = vector<int>(stops.size(), 0);
	S.passInRoute = vector<int>(k, 0);
	
	if (heuristic != 3) {
		//Make a minimal covering for the initial set of bus stops
		generateNewCovering(S.stopUsed, -1, heuristic);
	}
	else {
		getClosestStops(S.stopUsed);
	}
	
	//Assign each address to the closest used bus stop
	for (i = 0; i < addresses.size(); i++) {
		for (j = 0; j < addrAdjList[i].size(); j++) {
			if (S.stopUsed[addrAdjList[i][j]]) {
				S.assignedTo[i] = addrAdjList[i][j];
				break;
			}
		}
	}

	//Calculate the number boarding at each stop
	for (i = 0; i < addresses.size(); i++) {
		for (j = 0; j < addrAdjList[i].size(); j++) {
			if (S.stopUsed[addrAdjList[i][j]]) {
				S.numBoarding[addrAdjList[i][j]] += addresses[i].numPass;
				break;
			}
		}
	}

	//If there are any stops with no students assigned to them, delete them from the solution
	for (i = 1; i < stops.size(); i++) {
		if (S.numBoarding[i] <= 0) {
			S.stopUsed[i] = false;
		}
	}
		
	//Use BPP style procedure to pack all the children on to k buses. First Gather together the information on 
	//each stop that is being used and the number boarding there, then pack them
	stopsToPack.clear();
	weightOfStopsToPack.clear();
	for (i = 1; i < S.stopUsed.size(); i++) {
		if (S.stopUsed[i]) {
			stopsToPack.push_back(i);
			weightOfStopsToPack.push_back(S.numBoarding[i]);
		}
	}
	binPacker(S.items, S.W, S.passInRoute, stopsToPack, weightOfStopsToPack);

	//Finally, we need to repopulate the residual structures. 
	repopulateAuxiliaries(S);

	//...and calculate the costs
	S.cost = calcSolCostFromScratch(S);
	S.costWalk = calcWalkCostFromScratch(S);
}

extern vector<STOP> stops;
extern vector<ADDR> addresses;
extern vector<bool> isOutlier;
extern vector<vector<double> > dDist;
extern vector<vector<double> > dTime;
extern vector<vector<double> > wDist;
extern vector<vector<double> > wTime;
extern vector<vector<int> > stopAdjList;
extern vector<vector<int> > addrAdjList;
extern vector<vector<bool> > addrStopAdj;
extern int totalPassengers, maxBusCapacity;
extern double maxWalkDist;
extern double minEligibilityDist;
extern string distUnits;
extern double dwellPerPassenger;
extern double dwellPerStop;
extern double excessWeight;
extern double maxJourneyTime;
extern int verbosity;

//A "local" global variable for 
vector<int> tempVec1, tempVec2, tempVec3, tempVec4;

inline
double minVal(double a, double b) {
	if (a < b) return a; else return b;
}

inline
int minVal(int a, int b) {
	if (a < b) return a; else return b;
}

void twoOpt(vector<int> &S, int a, int b) {
	//Does a Two-Opt move
	int i = a, j = b;
	if (i > j) swapVals(i, j);
	while (i < j) {
		swapVals(S[i], S[j]);
		i++;
		j--;
	}
}

void updateSol(SOL &S, int r) {
	//Updates various data structures in the solution after changes have been made to S.items and S.W
	int passengers = 0, i;
	//Calculate the cost of the new route and keep track on the number of "feasible routes" in S
	bool routeHasOutlier = containsOutlierStop(S.items[r]);
	double newLen = calcRouteLenFromScratch(S, r);
	if (routeHasOutlier == true && S.hasOutlier[r] == false) S.numRoutesWithOutliers++;
	else if (routeHasOutlier == false && S.hasOutlier[r] == true) S.numRoutesWithOutliers--;

	if ( (routeHasOutlier || newLen <= maxJourneyTime) && !(S.routeLen[r] <= maxJourneyTime || S.hasOutlier[r]))
		S.numFeasibleRoutes++;
	else if (!(routeHasOutlier || newLen <= maxJourneyTime) && (S.routeLen[r] <= maxJourneyTime || S.hasOutlier[r]))
		S.numFeasibleRoutes--;

	S.hasOutlier[r] = routeHasOutlier;
	S.routeLen[r] = newLen;
	//Updatethe number of passengers in this route
	for (i = 0; i < S.W[r].size(); i++) 
		passengers += S.W[r][i];
	S.passInRoute[r] = passengers;
	//Update the posInRoute array
	for (i = 0; i < S.items[r].size(); i++) {
		S.posInRoute[S.items[r][i]][r] = i;
	}
}

void resetPosInRoute(SOL &S, int r) {
	//Used when a route r is about to be changed. Here, all non -1 values in column r are switched to -1s
	int i;
	for (i = 0; i < S.items[r].size(); i++) S.posInRoute[S.items[r][i]][r] = -1;
}

void removeElement(int x, vector<int> &A) {
	//Remove an element x from a vector A. (We assume there is exatly one occurence of x)
	int i;
	for (i = 0; i < A.size(); i++) if (A[i] == x) break;
	if (i >= A.size()) { cout << "Error. Element must be present\n"; exit(1); }
	swapVals(A[i], A.back());
	A.pop_back();
}

void updateRouteOfStops(SOL &S, int x, int y1, int y2, int i, int j1, int j2) {
	//Used when two routes, x and i, are about to be changed
	int y, j;
	for (y = y1; y < y2; y++) removeElement(x, S.routeOfStop[S.items[x][y]]);
	for (j = j1; j < j2; j++) removeElement(i, S.routeOfStop[S.items[i][j]]);
	for (y = y1; y < y2; y++) S.routeOfStop[S.items[x][y]].push_back(i);
	for (j = j1; j < j2; j++) S.routeOfStop[S.items[i][j]].push_back(x);
}

void updateCommonStopMatrix(SOL &S, int r) {
	//Updates the common stops matrix based on the move that has just been made 
	int i;
	for (i = 0; i < S.items.size(); i++) {
		if (i != r) {
			if (existsCommonStop(S, r, i)) {
				S.commonStop[i][r] = true;
				S.commonStop[r][i] = true;
			}
			else {
				S.commonStop[i][r] = false;
				S.commonStop[r][i] = false;
			}
		}
	}
}

int checkForPresence(SOL &S, int item, int r) {
	//Checks if "item" occurs in route r. If so its position is returned, else -1 is returned
	return (S.posInRoute[item][r]);
}

int checkForPresence(SOL &S, int item, int r, int a, int b) {
	//Checks if "item" occurs in positions [(0,...,(a - 1)] or [b,...,(n - 1)] of route r. If so its position is returned, else -1 is returned
	int pos = S.posInRoute[item][r];
	if (pos == -1 || (pos >= a && pos < b)) return -1;
	else return pos;
}

void insertSection(SOL &S, int x, int y1, int y2, int i, int j1) {
	//Inserts section from route x into route i and eliminates duplicates
	int y, pos;
	tempVec1.clear();
	tempVec2.clear();
	//Form the section to be inserted into i
	for (y = y1; y < y2; y++) {
		pos = checkForPresence(S, S.items[x][y], i);
		if (pos == -1) {
			//The item in route x at position y is not duplicated in route i, so simply copy the stop
			tempVec1.push_back(S.items[x][y]);
			tempVec2.push_back(S.W[x][y]);
		}
		else {
			//The item in route x at position y is duplicated in route i, so we don't copy it but re-assign the affected passengers
			S.W[i][pos] += S.W[x][y];
			S.solSize--;
		}
	}
	//Now insert these sections into i and delete from x
	resetPosInRoute(S, i);
	resetPosInRoute(S, x);

	//update the routeOfStops structure (cannot use the function above for doing this as some elements may have been eliminated
	for (y = y1; y < y2; y++) removeElement(x, S.routeOfStop[S.items[x][y]]);
	for (y = 0; y < tempVec1.size(); y++) S.routeOfStop[tempVec1[y]].push_back(i);

	S.items[i].insert(S.items[i].begin() + j1, tempVec1.begin(), tempVec1.end());
	S.items[x].erase(S.items[x].begin() + y1, S.items[x].begin() + y2);
	S.W[i].insert(S.W[i].begin() + j1, tempVec2.begin(), tempVec2.end());
	S.W[x].erase(S.W[x].begin() + y1, S.W[x].begin() + y2);
}

void swapSections(SOL &S, int x, int y1, int y2, int i, int j1, int j2) {
	//Swaps sections from route x and route i and eliminates duplicates
	int y, j, pos;
	tempVec1.clear();
	tempVec2.clear();
	tempVec3.clear();
	tempVec4.clear();
	//Form the section to be inserted into route i
	for (y = y1; y < y2; y++) {
		pos = checkForPresence(S, S.items[x][y], i, j1, j2);
		if (pos == -1) {
			//The item in route x at position y is not duplicated in route i (outside of the selected section), so simply copy the stop
			tempVec1.push_back(S.items[x][y]);
			tempVec2.push_back(S.W[x][y]);
		}
		else {
			//The item in route x at position y is duplicated in route i, so we don't copy it but need to re-assign the affected passengers
			//cout << "Removing instance of stopa " << S.items[x][y] << endl;
			S.W[i][pos] += S.W[x][y];
			S.solSize--;
		}
	}
	//Form the section to be inserted into route x
	for (j = j1; j < j2; j++) {
		pos = checkForPresence(S, S.items[i][j], x, y1, y2);
		if (pos == -1) {
			//The item in route i at position j is not duplicated in route x (outside of the selected section), so simply copy the stop
			tempVec3.push_back(S.items[i][j]);
			tempVec4.push_back(S.W[i][j]);
		}
		else {
			//The item in route i at position j is duplicated in route x, so we don't copy it but need to re-assign the affected passengers
			//cout << "Removing instance of stopb " << S.items[i][j] << endl;
			S.W[x][pos] += S.W[i][j];
			S.solSize--;
		}
	}
	resetPosInRoute(S, i);
	resetPosInRoute(S, x);
	
	//update the routeOfStops structure (cannot use the function above for doing this as some elements may have been eliminated
	for (y = y1; y < y2; y++) removeElement(x, S.routeOfStop[S.items[x][y]]);
	for (j = j1; j < j2; j++) removeElement(i, S.routeOfStop[S.items[i][j]]);
	for (y = 0; y < tempVec1.size(); y++) S.routeOfStop[tempVec1[y]].push_back(i);
	for (j = 0; j < tempVec3.size(); j++) S.routeOfStop[tempVec3[j]].push_back(x);

	//Reform route i
	S.items[i].erase(S.items[i].begin() + j1, S.items[i].begin() + j2);
	S.items[i].insert(S.items[i].begin() + j1, tempVec1.begin(), tempVec1.end());
	S.W[i].erase(S.W[i].begin() + j1, S.W[i].begin() + j2);
	S.W[i].insert(S.W[i].begin() + j1, tempVec2.begin(), tempVec2.end());
	//Reform route x	
	S.items[x].erase(S.items[x].begin() + y1, S.items[x].begin() + y2);
	S.items[x].insert(S.items[x].begin() + y1, tempVec3.begin(), tempVec3.end());
	S.W[x].erase(S.W[x].begin() + y1, S.W[x].begin() + y2);
	S.W[x].insert(S.W[x].begin() + y1, tempVec4.begin(), tempVec4.end());
}

void doMove1(SOL &S, int x, int y1, int y2, int i, double newCost, bool flippedx) {
	//Insert a section from x into the empty route i
	if (flippedx) {
		twoOpt(S.items[x], y1, y2 - 1);
		twoOpt(S.W[x], y1, y2 - 1);
	}
	resetPosInRoute(S, i);
	resetPosInRoute(S, x);
	updateRouteOfStops(S, x, y1, y2, i, 0, 0);
	if (!(y1 == 0 && y2 == S.items[x].size())) S.numEmptyRoutes--;
	S.items[i].insert(S.items[i].begin(), S.items[x].begin() + y1, S.items[x].begin() + y2);
	S.items[x].erase(S.items[x].begin() + y1, S.items[x].begin() + y2);
	S.W[i].insert(S.W[i].begin(), S.W[x].begin() + y1, S.W[x].begin() + y2);
	S.W[x].erase(S.W[x].begin() + y1, S.W[x].begin() + y2);
	updateCommonStopMatrix(S, x);
	updateCommonStopMatrix(S, i);
	updateSol(S, x);
	updateSol(S, i);
	S.cost = newCost;
}

void doMove2(SOL &S, int x, int y1, int y2, int i, int j1, double newCost, bool flippedx) {
	//Insert a section from route x into the non-empty route i
	if (y1 == 0 && y2 == S.items[x].size()) S.numEmptyRoutes++;
	if (flippedx) {
		twoOpt(S.items[x], y1, y2 - 1);
		twoOpt(S.W[x], y1, y2 - 1);
	}
	if (S.commonStop[x][i] == false) {
		//No common stops in routes i and x so can make the changes very simply
		resetPosInRoute(S, i);
		resetPosInRoute(S, x);
		updateRouteOfStops(S, x, y1, y2, i, 0, 0);
		S.items[i].insert(S.items[i].begin() + j1, S.items[x].begin() + y1, S.items[x].begin() + y2);
		S.items[x].erase(S.items[x].begin() + y1, S.items[x].begin() + y2);
		S.W[i].insert(S.W[i].begin() + j1, S.W[x].begin() + y1, S.W[x].begin() + y2);
		S.W[x].erase(S.W[x].begin() + y1, S.W[x].begin() + y2);
	}
	else {
		//Routes x and i contain common stops so we need to take care to delete these if they end up in the same route
		insertSection(S, x, y1, y2, i, j1);
	}
	updateCommonStopMatrix(S, x);
	updateCommonStopMatrix(S, i);
	updateSol(S, x);
	updateSol(S, i);
	S.cost = newCost;
}

void doMove3(SOL &S, int x, int y1, int y2, int i, int j1, int j2, double newCost, bool flippedx, bool flippedi) {
	//Swap a section from route x and a section from route i
	if (flippedx) {
		twoOpt(S.items[x], y1, y2 - 1);
		twoOpt(S.W[x], y1, y2 - 1);
	}
	if (flippedi) {
		twoOpt(S.items[i], j1, j2 - 1);
		twoOpt(S.W[i], j1, j2 - 1);
	}
	if (S.commonStop[x][i] == false) {
		//No common stops in routes i and x so can make the changes very simply
		resetPosInRoute(S, i);
		resetPosInRoute(S, x);
		updateRouteOfStops(S, x, y1, y2, i, j1, j2);
		tempVec1.clear();
		tempVec1.assign(S.items[i].begin() + j1, S.items[i].begin() + j2);
		S.items[i].erase(S.items[i].begin() + j1, S.items[i].begin() + j2);
		S.items[i].insert(S.items[i].begin() + j1, S.items[x].begin() + y1, S.items[x].begin() + y2);
		S.items[x].erase(S.items[x].begin() + y1, S.items[x].begin() + y2);
		S.items[x].insert(S.items[x].begin() + y1, tempVec1.begin(), tempVec1.end());
		tempVec1.clear();
		tempVec1.assign(S.W[i].begin() + j1, S.W[i].begin() + j2);
		S.W[i].erase(S.W[i].begin() + j1, S.W[i].begin() + j2);
		S.W[i].insert(S.W[i].begin() + j1, S.W[x].begin() + y1, S.W[x].begin() + y2);
		S.W[x].erase(S.W[x].begin() + y1, S.W[x].begin() + y2);
		S.W[x].insert(S.W[x].begin() + y1, tempVec1.begin(), tempVec1.end());
	}
	else {
		//Routes i and x contain common stops so we need to take care to delete these if they end up in the same route
		swapSections(S, x, y1, y2, i, j1, j2);
	}
	if (S.items[x].empty()) S.numEmptyRoutes++;
	if (S.items[i].empty()) S.numEmptyRoutes++;
	updateCommonStopMatrix(S, x);
	updateCommonStopMatrix(S, i);
	updateSol(S, x);
	updateSol(S, i);
	S.cost = newCost;
}

void doMove4(SOL &S, int x, int y1, int y2, double newCost){
	//Swap two stops in a route x
	resetPosInRoute(S, x);
	swapVals(S.items[x][y1], S.items[x][y2]);
	swapVals(S.W[x][y1], S.W[x][y2]);
	updateSol(S, x);
	S.cost = newCost;
}

void doMove5(SOL &S, int x, int y1, int y2, double newCost){
	//Do a two-opt in a single route x
	resetPosInRoute(S, x);
	twoOpt(S.items[x], y1, y2);
	twoOpt(S.W[x], y1, y2);
	updateSol(S, x);
	S.cost = newCost;
}

void doMove6(SOL &S, int x, int y1, int y2, int z, double newCost, bool flippedx) {
	//So an Or-opt on a single route x
	if (flippedx) {
		twoOpt(S.items[x], y1, y2);
		twoOpt(S.W[x], y1, y2);
	}
	resetPosInRoute(S, x);
	tempVec1.clear();
	tempVec1.assign(S.items[x].begin() + y1, S.items[x].begin() + (y2 + 1));
	S.items[x].erase(S.items[x].begin() + y1, S.items[x].begin() + (y2 + 1));
	if (y1 > z)		S.items[x].insert(S.items[x].begin() + z, tempVec1.begin(), tempVec1.end());
	else			S.items[x].insert(S.items[x].begin() + (z - tempVec1.size()), tempVec1.begin(), tempVec1.end());
	tempVec1.clear();
	tempVec1.assign(S.W[x].begin() + y1, S.W[x].begin() + (y2 + 1));
	S.W[x].erase(S.W[x].begin() + y1, S.W[x].begin() + (y2 + 1));
	if (y1 > z)		S.W[x].insert(S.W[x].begin() + z, tempVec1.begin(), tempVec1.end());
	else			S.W[x].insert(S.W[x].begin() + (z - tempVec1.size()), tempVec1.begin(), tempVec1.end());
	updateSol(S, x);
	S.cost = newCost;
}

void doMove7(SOL &S, int x, int i, int j, double newCost) {
	int u, v = S.items[i][j], pos = S.posInRoute[v][x], bestInsertPos = -1, spareCapX = maxBusCapacity - S.passInRoute[x], toTransfer;
	double minCost, inserCost;
	if (pos == -1 && S.items[x].size() > 0) {
		//Stop v is not in nonempty route x, so we ID the best point to insert it (before stop "bestInsertPos")
		minCost = dTime[v][S.items[x][0]];
		bestInsertPos = 0;
		for (u = 1; u < S.items[x].size(); u++) {
			inserCost = dTime[S.items[x][u - 1]][v] + dTime[v][S.items[x][u]] - dTime[S.items[x][u - 1]][S.items[x][u]];
			if(inserCost < minCost){
				minCost = inserCost;
				bestInsertPos = u;
			}
		}
		inserCost = dTime[S.items[x].back()][v] + dTime[v][0] - dTime[S.items[x].back()][0];
		if (inserCost < minCost) {
			minCost = inserCost;
			bestInsertPos = S.items[x].size();
		}
	}
	//Now calculate how many passengers we will transfer from v in route i, to v in route j
	if (S.routeLen[i] < maxJourneyTime) toTransfer = 1;
	else toTransfer = minVal(S.W[i][j] - 1, spareCapX);
	//Now do the move
	if (pos != -1) {
		//We are just transferring passengers between existing multistops
		S.W[i][j] -= toTransfer;
		S.W[x][pos] += toTransfer;
		updateSol(S, i);
		updateSol(S, x);
		S.cost = newCost;
	}
	else if (S.items[x].empty()) {
		//We are inserting a copy of v into an empty route
		S.W[i][j] -= toTransfer;
		S.items[x].push_back(v);
		S.W[x].push_back(toTransfer);
		S.routeOfStop[v].push_back(x);
		updateCommonStopMatrix(S, x);
		updateCommonStopMatrix(S, i);
		updateSol(S, i);
		updateSol(S, x);
		S.cost = newCost;
		S.numEmptyRoutes--;
		S.solSize++;
	}
	else {
		//We are making a copy of v and inserting it into position "bestInsertPos"
		S.W[i][j] -= toTransfer;
		S.items[x].insert(S.items[x].begin() + bestInsertPos, v);
		S.W[x].insert(S.W[x].begin() + bestInsertPos, toTransfer);
		S.routeOfStop[v].push_back(x);
		updateCommonStopMatrix(S, x);
		updateCommonStopMatrix(S, i);
		updateSol(S, i);
		updateSol(S, x);
		S.cost = newCost;
		S.solSize++;
	}
}

void evaluateOrOpt(double &newCost, SOL &S, int route, int x, int y, int z, EVALINFO &info)
{
	//Evaluate the effect of removing sequence (x,....,y) reinserting before pos z
	int n = S.items[route].size();
	double newLen, newLenF;
	if (z >= x && z <= y + 1) {
		cout << "Error should not be here\n"; 
		exit(1);
	} 
	else if (x == 0 && z == n) {
		newLen = S.routeLen[route] - dTime[S.items[route][y]][S.items[route][y + 1]] - dTime[S.items[route][z - 1]][0] + dTime[S.items[route][z - 1]][S.items[route][x]] + dTime[S.items[route][y]][0];
		newLenF = S.routeLen[route] - dTime[S.items[route][y]][S.items[route][y + 1]] - dTime[S.items[route][z - 1]][0] + dTime[S.items[route][z - 1]][S.items[route][y]] + dTime[S.items[route][x]][0] - info.innerX + info.innerXF;
	}
	else if (x == 0) {
		newLen = S.routeLen[route] - dTime[S.items[route][y]][S.items[route][y + 1]] - dTime[S.items[route][z - 1]][S.items[route][z]] + dTime[S.items[route][z - 1]][S.items[route][x]] + dTime[S.items[route][y]][S.items[route][z]];
		newLenF = S.routeLen[route] - dTime[S.items[route][y]][S.items[route][y + 1]] - dTime[S.items[route][z - 1]][S.items[route][z]] + dTime[S.items[route][z - 1]][S.items[route][y]] + dTime[S.items[route][x]][S.items[route][z]] - info.innerX + info.innerXF;
	}
	else if (z == n) {
		newLen = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][S.items[route][y + 1]] - dTime[S.items[route][z - 1]][0] + dTime[S.items[route][x - 1]][S.items[route][y + 1]] + dTime[S.items[route][z - 1]][S.items[route][x]] + dTime[S.items[route][y]][0];
		newLenF = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][S.items[route][y + 1]] - dTime[S.items[route][z - 1]][0] + dTime[S.items[route][x - 1]][S.items[route][y + 1]] + dTime[S.items[route][z - 1]][S.items[route][y]] + dTime[S.items[route][x]][0] - info.innerX + info.innerXF;
	}
	else if (y == n - 1 && z == 0) {
		newLen = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][0] + dTime[S.items[route][x - 1]][0] + dTime[S.items[route][y]][S.items[route][z]];
		newLenF = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][0] + dTime[S.items[route][x - 1]][0] + dTime[S.items[route][x]][S.items[route][z]] - info.innerX + info.innerXF;
	}
	else if (y == n - 1) {
		newLen = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][0] - dTime[S.items[route][z - 1]][S.items[route][z]] + dTime[S.items[route][x - 1]][0] + dTime[S.items[route][z - 1]][S.items[route][x]] + dTime[S.items[route][y]][S.items[route][z]];
		newLenF = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][0] - dTime[S.items[route][z - 1]][S.items[route][z]] + dTime[S.items[route][x - 1]][0] + dTime[S.items[route][z - 1]][S.items[route][y]] + dTime[S.items[route][x]][S.items[route][z]] - info.innerX + info.innerXF;
	}
	else if (z == 0) {
		newLen = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][S.items[route][y + 1]] + dTime[S.items[route][x - 1]][S.items[route][y + 1]] + dTime[S.items[route][y]][S.items[route][z]];
		newLenF = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][S.items[route][y + 1]] + dTime[S.items[route][x - 1]][S.items[route][y + 1]] + dTime[S.items[route][x]][S.items[route][z]] - info.innerX + info.innerXF;
	}
	else {
		newLen = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][S.items[route][y + 1]] - dTime[S.items[route][z - 1]][S.items[route][z]] + dTime[S.items[route][z - 1]][S.items[route][x]] + dTime[S.items[route][y]][S.items[route][z]] + dTime[S.items[route][x - 1]][S.items[route][y + 1]];
		newLenF = S.routeLen[route] - dTime[S.items[route][x - 1]][S.items[route][x]] - dTime[S.items[route][y]][S.items[route][y + 1]] - dTime[S.items[route][z - 1]][S.items[route][z]] + dTime[S.items[route][z - 1]][S.items[route][y]] + dTime[S.items[route][x]][S.items[route][z]] + dTime[S.items[route][x - 1]][S.items[route][y + 1]] - info.innerX + info.innerXF;
	}
	if (newLen <= newLenF) info.flippedX = false;
	else info.flippedX = true;
	newLen = minVal(newLen, newLenF);
	newCost = S.cost - calcRCost(S.routeLen[route]) + calcRCost(newLen);
}
	
void evaluateSwapTwoOpt(double &newCost, SOL &S, int route, int x, int y, int moveType, EVALINFO &info)
{
	if (x == y) { newCost = S.cost;	return; }
	//Given current solution and cost, calculates the new cost according to x <= y and moveType
	int xl = x - 1, xr = x + 1, yl = y - 1, yr = y + 1, n = S.items[route].size();
	double newLen;
	if (moveType == 5 || x == y - 1) {
		//Evaluating a twoOpt. NB: A two-opt with 2 consecutive locations is the same as a swap
		if (x == 0 && y == n - 1)	newLen = S.routeLen[route] - dTime[S.items[route][y]][0] + dTime[S.items[route][x]][0] - info.innerX + info.innerXF;
		else if (x == 0)			newLen = S.routeLen[route] - dTime[S.items[route][y]][S.items[route][yr]] + dTime[S.items[route][x]][S.items[route][yr]] - info.innerX + info.innerXF;
		else if (y == n - 1)		newLen = S.routeLen[route] - dTime[S.items[route][xl]][S.items[route][x]] - dTime[S.items[route][y]][0] + dTime[S.items[route][xl]][S.items[route][y]] + dTime[S.items[route][x]][0] - info.innerX + info.innerXF;
		else						newLen = S.routeLen[route] - dTime[S.items[route][xl]][S.items[route][x]] - dTime[S.items[route][y]][S.items[route][yr]] + dTime[S.items[route][xl]][S.items[route][y]] + dTime[S.items[route][x]][S.items[route][yr]] - info.innerX + info.innerXF;
	}
	else {
		//Evaluating a swap (the swapping of two consecutive elements is covered above)
		if (x == 0 && y == n - 1)	newLen = S.routeLen[route] - dTime[S.items[route][x]][S.items[route][xr]] - dTime[S.items[route][yl]][S.items[route][y]] - dTime[S.items[route][y]][0] + dTime[S.items[route][y]][S.items[route][xr]] + dTime[S.items[route][yl]][S.items[route][x]] + dTime[S.items[route][x]][0];
		else if (x == 0)			newLen = S.routeLen[route] - dTime[S.items[route][x]][S.items[route][xr]] - dTime[S.items[route][yl]][S.items[route][y]] - dTime[S.items[route][y]][S.items[route][yr]] + dTime[S.items[route][y]][S.items[route][xr]] + dTime[S.items[route][yl]][S.items[route][x]] + dTime[S.items[route][x]][S.items[route][yr]];
		else if (y == n - 1)		newLen = S.routeLen[route] - dTime[S.items[route][xl]][S.items[route][x]] - dTime[S.items[route][x]][S.items[route][xr]] - dTime[S.items[route][yl]][S.items[route][y]] - dTime[S.items[route][y]][0] + dTime[S.items[route][xl]][S.items[route][y]] + dTime[S.items[route][y]][S.items[route][xr]] + dTime[S.items[route][yl]][S.items[route][x]] + dTime[S.items[route][x]][0];
		else						newLen = S.routeLen[route] - dTime[S.items[route][xl]][S.items[route][x]] - dTime[S.items[route][x]][S.items[route][xr]] - dTime[S.items[route][yl]][S.items[route][y]] - dTime[S.items[route][y]][S.items[route][yr]] + dTime[S.items[route][xl]][S.items[route][y]] + dTime[S.items[route][y]][S.items[route][xr]] + dTime[S.items[route][yl]][S.items[route][x]] + dTime[S.items[route][x]][S.items[route][yr]];
	}
	newCost = S.cost - calcRCost(S.routeLen[route]) + calcRCost(newLen);
}

void evaluateInterEmpty(double &newCost, SOL &S, int i, int x, int y1, int y2, EVALINFO &info)
{
	//We are inserting a section from route x into the empty route i. Calculate the result of doing this
	double newLenx, newLeni, newLeniF;
	newLeni = dTime[S.items[x][y2 - 1]][0] + info.innerX + info.dwellXSection;
	newLeniF = dTime[S.items[x][y1]][0] + info.innerXF + info.dwellXSection;
	//Determine which is better and proceed with this result
	if (newLeni <= newLeniF) info.flippedX = false;
	else info.flippedX = true;
	newLeni = minVal(newLeni, newLeniF);
	//Also calculate the result of removing the section from x 
	if (y1 == 0) {
		if (y2 == S.items[x].size())		newLenx = S.routeLen[x] - dTime[S.items[x][y2 - 1]][0] - info.innerX - info.dwellXSection;
		else								newLenx = S.routeLen[x] - dTime[S.items[x][y2 - 1]][S.items[x][y2]] - info.innerX - info.dwellXSection;
	}
	else if (y2 == S.items[x].size())		newLenx = S.routeLen[x] - dTime[S.items[x][y1 - 1]][S.items[x][y1]] - dTime[S.items[x][y2 - 1]][0] + dTime[S.items[x][y1 - 1]][0] - info.innerX - info.dwellXSection;
	else									newLenx = S.routeLen[x] - dTime[S.items[x][y1 - 1]][S.items[x][y1]] - dTime[S.items[x][y2 - 1]][S.items[x][y2]] + dTime[S.items[x][y1 - 1]][S.items[x][y2]] - info.innerX - info.dwellXSection;
	newCost = S.cost - calcRCost(S.routeLen[x])	+ calcRCost(newLenx) + calcRCost(newLeni);
}

double calcRealInsertCost(SOL &S, int i, int j1, vector<int> &xSection, double internalX, EVALINFO &info) {
	//We are INSERTING xSection before position S.items[i][j1]. Calculate the result of doing this
	if (xSection.empty())
		return S.routeLen[i] + info.dwellXSection;
	else if (j1 == 0) 
		return S.routeLen[i] + dTime[xSection.back()][S.items[i][j1]] + internalX + info.dwellXSection;
	else if (j1 == S.items[i].size()) 
		return S.routeLen[i] - dTime[S.items[i][j1 - 1]][0] + dTime[S.items[i][j1 - 1]][xSection.front()] + dTime[xSection.back()][0] + internalX + info.dwellXSection;
	else 
		return S.routeLen[i] - dTime[S.items[i][j1 - 1]][S.items[i][j1]] + dTime[S.items[i][j1 - 1]][xSection.front()] + dTime[xSection.back()][S.items[i][j1]] + internalX + info.dwellXSection;
}

void evaluateInsert(double &newCost, SOL &S, int i, int j1, int x, int y1, int y2, EVALINFO &info)
{
	double newLenx, newLeni, newLeniF;
	//We are insertnig a section from route x before position j1 in route i. Calculate the result of doing this
	if (j1 == 0)						newLeni = S.routeLen[i] + dTime[S.items[x][y2 - 1]][S.items[i][j1]] + info.innerX + info.dwellXSection;
	else if (j1 == S.items[i].size())	newLeni = S.routeLen[i] - dTime[S.items[i][j1 - 1]][0] + dTime[S.items[i][j1 - 1]][S.items[x][y1]] + dTime[S.items[x][y2 - 1]][0] + info.innerX + info.dwellXSection;
	else								newLeni = S.routeLen[i] - dTime[S.items[i][j1 - 1]][S.items[i][j1]] + dTime[S.items[i][j1 - 1]][S.items[x][y1]] + dTime[S.items[x][y2 - 1]][S.items[i][j1]] + info.innerX + info.dwellXSection;
	//Calculate the result of inserting the section flipped 
	if (j1 == 0)						newLeniF = S.routeLen[i] + dTime[S.items[x][y1]][S.items[i][j1]] + info.innerXF + info.dwellXSection;
	else if (j1 == S.items[i].size())	newLeniF = S.routeLen[i] - dTime[S.items[i][j1 - 1]][0] + dTime[S.items[i][j1 - 1]][S.items[x][y2 - 1]] + dTime[S.items[x][y1]][0] + info.innerXF + info.dwellXSection;
	else								newLeniF = S.routeLen[i] - dTime[S.items[i][j1 - 1]][S.items[i][j1]] + dTime[S.items[i][j1 - 1]][S.items[x][y2 - 1]] + dTime[S.items[x][y1]][S.items[i][j1]] + info.innerXF + info.dwellXSection;
	//Determine which is better and proceed with this result
	if (newLeni <= newLeniF) info.flippedX = false;
	else info.flippedX = true;
	newLeni = minVal(newLeni, newLeniF);
	//Finally calculate the result of removing the section from route x
	if (y1 == 0) {
		if (y2 == S.items[x].size())	newLenx = S.routeLen[x] - dTime[S.items[x][y2 - 1]][0] - info.innerX - info.dwellXSection;
		else							newLenx = S.routeLen[x] - dTime[S.items[x][y2 - 1]][S.items[x][y2]] - info.innerX - info.dwellXSection;
	}
	else if (y2 == S.items[x].size())	newLenx = S.routeLen[x] - dTime[S.items[x][y1 - 1]][S.items[x][y1]] - dTime[S.items[x][y2 - 1]][0] + dTime[S.items[x][y1 - 1]][0] - info.innerX - info.dwellXSection;
	else								newLenx = S.routeLen[x] - dTime[S.items[x][y1 - 1]][S.items[x][y1]] - dTime[S.items[x][y2 - 1]][S.items[x][y2]] + dTime[S.items[x][y1 - 1]][S.items[x][y2]] - info.innerX - info.dwellXSection;
	
	if (S.commonStop[x][i]) {
		//If we are here we also need to cope with any duplicates and re-evaluate the routes with their removal
		int y, pos;
		double internalX = 0.0, dwellXSaving = 0.0;
		bool dupInXSec = false;
		tempVec1.clear();
		//First flip the x section if needed
		if (info.flippedX) { twoOpt(S.items[x], y1, y2 - 1); twoOpt(S.W[x], y1, y2 - 1); }
		//And build up the actual x section that will be inserted into route i
		for (y = y1; y < y2; y++) {
			pos = checkForPresence(S, S.items[x][y], i);
			if (pos == -1) {
				//The item in route x at position y is not duplicated in route i, so it isn't removed
				tempVec1.push_back(S.items[x][y]);
				if (tempVec1.size() > 1) internalX += dTime[tempVec1[tempVec1.size() - 2]][tempVec1.back()];
			}
			else {
				//The item in route x's section at position y is duplicated in route i, so we don't copy it and we record the associted stopping time
				dwellXSaving += calcDwellTime(0);
				dupInXSec = true;
			}
		}
		//If there is a duplicate somewhere, we recalculate the move, otherwise our previous calculation was correct
		if (dupInXSec) {
			newLeni = calcRealInsertCost(S, i, j1, tempVec1, internalX, info) - dwellXSaving;
		}
		//Flip the x section back if needed
		if (info.flippedX) { twoOpt(S.items[x], y1, y2 - 1); twoOpt(S.W[x], y1, y2 - 1); }
	}
	newCost = S.cost - calcRCost(S.routeLen[x])	- calcRCost(S.routeLen[i]) + calcRCost(newLenx) + calcRCost(newLeni);
}

void calcRealInterCost(double &newLenx, double &newLeni, SOL &S, int x, int y1, int y2, int i, int j1, int j2, 
	vector<int> &xSection, vector<int> &iSection, double internalX, double internalI, EVALINFO &info,
	double lenXSecRemoved, double lenISecRemoved) {
	//We are swapping xSection and iSection. Calculate the result of doing this with the altered sections
	if (xSection.empty())					newLeni = lenISecRemoved + info.dwellXSection;
	else {
		if (j1 == 0)
			if (j2 == S.items[i].size())	newLeni = lenISecRemoved + dTime[xSection.back()][0] + internalX + info.dwellXSection;
			else							newLeni = lenISecRemoved + dTime[xSection.back()][S.items[i][j2]] + internalX + info.dwellXSection;
		else if (j2 == S.items[i].size())	newLeni = lenISecRemoved - dTime[S.items[i][j1 - 1]][0] + dTime[S.items[i][j1 - 1]][xSection.front()] + dTime[xSection.back()][0] + internalX + info.dwellXSection;
		else								newLeni = lenISecRemoved - dTime[S.items[i][j1 - 1]][S.items[i][j2]] + dTime[S.items[i][j1 - 1]][xSection.front()] + dTime[xSection.back()][S.items[i][j2]] + internalX + info.dwellXSection;
	}
	if (iSection.empty())					newLenx = lenXSecRemoved + info.dwellISection;
	else {
		if (y1 == 0)
			if (y2 == S.items[x].size())	newLenx = lenXSecRemoved + dTime[iSection.back()][0] + internalI + info.dwellISection;
			else							newLenx = lenXSecRemoved + dTime[iSection.back()][S.items[x][y2]] + internalI + info.dwellISection;
		else if (y2 == S.items[x].size())	newLenx = lenXSecRemoved - dTime[S.items[x][y1 - 1]][0] + dTime[S.items[x][y1 - 1]][iSection.front()] + dTime[iSection.back()][0] + internalI + info.dwellISection;
		else								newLenx = lenXSecRemoved - dTime[S.items[x][y1 - 1]][S.items[x][y2]] + dTime[S.items[x][y1 - 1]][iSection.front()] + dTime[iSection.back()][S.items[x][y2]] + internalI + info.dwellISection;
	}
}

void evaluateInter(double &newCost, SOL &S, int i, int j1, int j2, int x, int y1, int y2, EVALINFO &info)
{
	double newLenx, newLeni, newLenxF, newLeniF, lenXSecRemoved, lenISecRemoved;
	//We are swapping a nonempty section from route x with a nonempty section in route i. First calculate the result of removing the two sections)
	if (y1 == 0) {
		if (y2 == S.items[x].size())	lenXSecRemoved = S.routeLen[x] - dTime[S.items[x][y2 - 1]][0] - info.innerX - info.dwellXSection;
		else							lenXSecRemoved = S.routeLen[x] - dTime[S.items[x][y2 - 1]][S.items[x][y2]] - info.innerX - info.dwellXSection;
	}
	else if (y2 == S.items[x].size())	lenXSecRemoved = S.routeLen[x] - dTime[S.items[x][y1 - 1]][S.items[x][y1]] - dTime[S.items[x][y2 - 1]][0] + dTime[S.items[x][y1 - 1]][0] - info.innerX - info.dwellXSection;
	else								lenXSecRemoved = S.routeLen[x] - dTime[S.items[x][y1 - 1]][S.items[x][y1]] - dTime[S.items[x][y2 - 1]][S.items[x][y2]] + dTime[S.items[x][y1 - 1]][S.items[x][y2]] - info.innerX - info.dwellXSection;
	if (j1 == 0) {
		if (j2 == S.items[i].size())	lenISecRemoved = S.routeLen[i] - dTime[S.items[i][j2 - 1]][0] - info.innerI - info.dwellISection;
		else							lenISecRemoved = S.routeLen[i] - dTime[S.items[i][j2 - 1]][S.items[i][j2]] - info.innerI - info.dwellISection;
	}
	else if (j2 == S.items[i].size())	lenISecRemoved = S.routeLen[i] - dTime[S.items[i][j1 - 1]][S.items[i][j1]] - dTime[S.items[i][j2 - 1]][0] + dTime[S.items[i][j1 - 1]][0] - info.innerI - info.dwellISection;
	else								lenISecRemoved = S.routeLen[i] - dTime[S.items[i][j1 - 1]][S.items[i][j1]] - dTime[S.items[i][j2 - 1]][S.items[i][j2]] + dTime[S.items[i][j1 - 1]][S.items[i][j2]] - info.innerI - info.dwellISection;
	//Now calculate result of inserting the x section at position j1 in route i.
	if (j1 == 0)
		if (j2 == S.items[i].size())	newLeni = lenISecRemoved + dTime[S.items[x][y2 - 1]][0] + info.innerX + info.dwellXSection;
		else							newLeni = lenISecRemoved + dTime[S.items[x][y2 - 1]][S.items[i][j2]] + info.innerX + info.dwellXSection;
	else if (j2 == S.items[i].size())	newLeni = lenISecRemoved - dTime[S.items[i][j1 - 1]][0] + dTime[S.items[i][j1 - 1]][S.items[x][y1]] + dTime[S.items[x][y2 - 1]][0] + info.innerX + info.dwellXSection;
	else								newLeni = lenISecRemoved - dTime[S.items[i][j1 - 1]][S.items[i][j2]] + dTime[S.items[i][j1 - 1]][S.items[x][y1]] + dTime[S.items[x][y2 - 1]][S.items[i][j2]] + info.innerX + info.dwellXSection;
	//and the same flipped
	if (j1 == 0)
		if (j2 == S.items[i].size())	newLeniF = lenISecRemoved + dTime[S.items[x][y1]][0] + info.innerXF + info.dwellXSection;
		else							newLeniF = lenISecRemoved + dTime[S.items[x][y1]][S.items[i][j2]] + info.innerXF + info.dwellXSection;
	else if (j2 == S.items[i].size())	newLeniF = lenISecRemoved - dTime[S.items[i][j1 - 1]][0] + dTime[S.items[i][j1 - 1]][S.items[x][y2 - 1]] + dTime[S.items[x][y1]][0] + info.innerXF + info.dwellXSection;
	else								newLeniF = lenISecRemoved - dTime[S.items[i][j1 - 1]][S.items[i][j2]] + dTime[S.items[i][j1 - 1]][S.items[x][y2 - 1]] + dTime[S.items[x][y1]][S.items[i][j2]] + info.innerXF + info.dwellXSection;
	if (newLeni <= newLeniF) info.flippedX = false;
	else info.flippedX = true;
	newLeni = minVal(newLeni, newLeniF);
	//Now calculate result of inserting the i section at position y1 in route x.
	if (y1 == 0)
		if (y2 == S.items[x].size())	newLenx = lenXSecRemoved + dTime[S.items[i][j2 - 1]][0] + info.innerI + info.dwellISection;
		else							newLenx = lenXSecRemoved + dTime[S.items[i][j2 - 1]][S.items[x][y2]] + info.innerI + info.dwellISection;
	else if (y2 == S.items[x].size())	newLenx = lenXSecRemoved - dTime[S.items[x][y1 - 1]][0] + dTime[S.items[x][y1 - 1]][S.items[i][j1]] + dTime[S.items[i][j2 - 1]][0] + info.innerI + info.dwellISection;
	else								newLenx = lenXSecRemoved - dTime[S.items[x][y1 - 1]][S.items[x][y2]] + dTime[S.items[x][y1 - 1]][S.items[i][j1]] + dTime[S.items[i][j2 - 1]][S.items[x][y2]] + info.innerI + info.dwellISection;
	//and the same flipped
	if (y1 == 0)
		if (y2 == S.items[x].size())	newLenxF = lenXSecRemoved + dTime[S.items[i][j1]][0] + info.innerIF + info.dwellISection;
		else							newLenxF = lenXSecRemoved + dTime[S.items[i][j1]][S.items[x][y2]] + info.innerIF + info.dwellISection;
	else if (y2 == S.items[x].size())	newLenxF = lenXSecRemoved - dTime[S.items[x][y1 - 1]][0] + dTime[S.items[x][y1 - 1]][S.items[i][j2 - 1]] + dTime[S.items[i][j1]][0] + info.innerIF + info.dwellISection;
	else								newLenxF = lenXSecRemoved - dTime[S.items[x][y1 - 1]][S.items[x][y2]] + dTime[S.items[x][y1 - 1]][S.items[i][j2 - 1]] + dTime[S.items[i][j1]][S.items[x][y2]] + info.innerIF + info.dwellISection;
	if (newLenx <= newLenxF) info.flippedI = false;
	else info.flippedI = true;
	newLenx = minVal(newLenx, newLenxF);
	
	if (S.commonStop[x][i]) {
		//If we are here we need to cope with any duplicates and re-evaluate the routes with their removal
		int y, j, pos;
		double internalX = 0.0, internalI = 0.0, dwellXSaving = 0.0, dwellISaving = 0.0;
		bool dupInXSec = false, dupInISec = false;
		tempVec1.clear(); tempVec2.clear();
		if (info.flippedX) { twoOpt(S.items[x], y1, y2 - 1); twoOpt(S.W[x], y1, y2 - 1); }
		if (info.flippedI) { twoOpt(S.items[i], j1, j2 - 1); twoOpt(S.W[i], j1, j2 - 1); }
		//Build up the actual x section that will be inserted into route i
		for (y = y1; y < y2; y++) {
			pos = checkForPresence(S, S.items[x][y], i, j1, j2);
			if (pos == -1) {
				//The item in route x at position y is not duplicated in route i, so it isn't removed
				tempVec1.push_back(S.items[x][y]);
				if (tempVec1.size() > 1) internalX += dTime[tempVec1[tempVec1.size() - 2]][tempVec1.back()];
			}
			else {
				//The item in route x at position y is duplicated in route i, so we don't copy it and we remove the associted stoppIng time
				dwellXSaving += calcDwellTime(0);
				dupInXSec = true;
			}
		}
		//And build up the actual i section that will be inserted into route x
		for (j = j1; j < j2; j++) {
			pos = checkForPresence(S, S.items[i][j], x, y1, y2);
			if (pos == -1) {
				//The item in route i at position j is not duplicated in route x, so it isn't removed
				tempVec2.push_back(S.items[i][j]);
				if (tempVec2.size() > 1) internalI += dTime[tempVec2[tempVec2.size() - 2]][tempVec2.back()];
			}
			else {
				//The item in route x at position y is duplicated in route i, so we don't copy it and we remove the associted stoppIng time
				dwellISaving += calcDwellTime(0);
				dupInISec = true;
			}
		}
		if (dupInXSec || dupInISec) {
			calcRealInterCost(newLenx, newLeni, S, x, y1, y2, i, j1, j2, tempVec1, tempVec2, internalX, internalI, info, lenXSecRemoved, lenISecRemoved);
			newLenx = newLenx - dwellISaving;
			newLeni = newLeni - dwellXSaving;
		}
		if (info.flippedX) { twoOpt(S.items[x], y1, y2 - 1); twoOpt(S.W[x], y1, y2 - 1); }
		if (info.flippedI) { twoOpt(S.items[i], j1, j2 - 1); twoOpt(S.W[i], j1, j2 - 1); }
	}
	newCost = S.cost - calcRCost(S.routeLen[x]) - calcRCost(S.routeLen[i]) + calcRCost(newLenx) + calcRCost(newLeni);
}

void evaluateVertexCopy(double &newCost, SOL &S, int i, int j, int x) {
	//Evaluate effect of copying v = S[i][j] into route x and then transferring some passengers to it
	//Need to assume that the num of people boarding at S[i][j] is >= 2 and that spare capacity in route x is >= 1
	if (S.W[i][j] < 2 || maxBusCapacity - S.passInRoute[x] < 1) {
		cout << "Error. Conditions not met for evaluateVertexCopy fn\n"; exit(1);
	}
	int v = S.items[i][j], pos = S.posInRoute[v][x], bestInsertPos = -1, spareCapX = maxBusCapacity - S.passInRoute[x], toTransfer;
	double minCost, inserCost;

	if (pos == -1 && S.items[x].size() > 0) {
		//Stop v is not in nonempty route x, so we look for the best point to insert it (before stop "bestInsertPos")
		minCost = dTime[v][S.items[x][0]];
		bestInsertPos = 0;
		for (int u = 1; u < S.items[x].size(); u++) {
			inserCost = dTime[S.items[x][u - 1]][v] + dTime[v][S.items[x][u]] - dTime[S.items[x][u - 1]][S.items[x][u]];
			if (inserCost < minCost) {
				minCost = inserCost;
				bestInsertPos = u;
			}
		}
		inserCost = dTime[S.items[x].back()][v] + dTime[v][0] - dTime[S.items[x].back()][0];
		if (inserCost < minCost) {
			minCost = inserCost;
			bestInsertPos = S.items[x].size();
		}
	}
	//Calculate how many passengers we'll transfer from v in route i, to v in route j
	if (S.routeLen[i] < maxJourneyTime) toTransfer = 1;
	else toTransfer = minVal(S.W[i][j] - 1, spareCapX);
	//Now calculate cost of the resultant solution if we were to do this move.
	double newLeni, newLenx;
	if (pos != -1) {
		//We're just transferring passengers between existing multistops
		newLeni = S.routeLen[i] - (dwellPerPassenger * toTransfer);
		newLenx = S.routeLen[x] + (dwellPerPassenger * toTransfer);
	}
	else if (S.items[x].empty()) {
		//We're inserting a copy of v into an empty route
		newLeni = S.routeLen[i] - (dwellPerPassenger * toTransfer);
		newLenx = S.routeLen[x] + dTime[v][0] + calcDwellTime(toTransfer);
	}
	else {
		//We're making a copy of v and putting it into a nonempty route
		newLeni = S.routeLen[i] - (dwellPerPassenger * toTransfer);
		if (bestInsertPos == 0)
			newLenx = S.routeLen[x] + dTime[v][S.items[x][0]] + calcDwellTime(toTransfer);
		else if (bestInsertPos == S.items[x].size())
			newLenx = S.routeLen[x] + dTime[S.items[x].back()][v] + dTime[v][0] + calcDwellTime(toTransfer) - dTime[S.items[x].back()][0];
		else
			newLenx = S.routeLen[x] + dTime[S.items[x][bestInsertPos - 1]][v] + dTime[v][S.items[x][bestInsertPos]] + calcDwellTime(toTransfer) - dTime[S.items[x][bestInsertPos - 1]][S.items[x][bestInsertPos]];
	}
	newCost = S.cost - calcRCost(S.routeLen[i]) - calcRCost(S.routeLen[x]) + calcRCost(newLeni) + calcRCost(newLenx);
}

bool localSearch(SOL &S, double &feasRatio, int &numMoves)
{
	int x, y1, y2, i, j1, j2, z, chosenMove;
	int besti, bestj1, bestj2, bestx, besty1, besty2, bestz, numBest = 0;
	double newCost = 0, bestCost = 0;
	long evalCnt = 0, evalFeasCnt = 0;
	bool checkedEmpty, bestflippedx, bestflippedi;
	EVALINFO info;
	feasRatio = 0.0;
	numMoves = 0;
	vector<vector<int> > tempW;
	vector<double> tempRouteLen;
	vector<int> tempPassInRoute;

	while (true) {
		chosenMove = 0;
		bestCost = DBL_MAX;
		numBest = 0;
		for (x = 0; x < S.items.size(); x++) {
			/*Inter-route operators. Check cost of swapping sections (S[x][y1]...S[x][y2-1]) and sections (S[i][j1]...S[i][j2-1]).
			where x != i. The latter section can be empty (j1==j2) in which case we insert (S[x][y1]...S[x][y2-1]) before the
			position S[i][j1]. Route i can also be empty. If there is more than one empty route i, only one of these is evaluated*/
			for (y1 = 0; y1 < S.items[x].size(); y1++) {
				info.innerX = 0.0;
				info.innerXF = 0.0;
				info.dwellXSection = 0.0;
				info.passXSection = 0;
				for (y2 = y1 + 1; y2 <= S.items[x].size(); y2++) {
					//Keep track of the total costs of the inernal edges in this section of route x (fwd and bkwds)
					if (y2 > y1 + 1) {
						info.innerX += dTime[S.items[x][y2 - 2]][S.items[x][y2 - 1]];
						info.innerXF += dTime[S.items[x][y2 - 1]][S.items[x][y2 - 2]];
					}
					//Also keep track of the total dwell times in this section of route x
					info.dwellXSection += calcDwellTime(S.W[x][y2 - 1]);
					info.passXSection += S.W[x][y2 - 1];
					checkedEmpty = false;
					for (i = 0; i < S.items.size(); i++) {
						if (x != i) {
							if (S.items[i].empty() && checkedEmpty == false) {
								//The neighbourhood operator involves one non-empty routes (x) and one empty route (i)
								evaluateInterEmpty(newCost, S, i, x, y1, y2, info);
								if (newCost <= bestCost) {
									if (newCost < bestCost) numBest = 0;
									if (rand() % (numBest + 1) == 0) {
										//Save the move with a certain probability
										chosenMove = 1;
										bestCost = newCost; besti = i; bestx = x; besty1 = y1; besty2 = y2; bestflippedx = info.flippedX;
									}
									numBest++;
								}
								checkedEmpty = true;
							}
							else {
								//The neighbourhood operator involves two non-empty routes, so loop through each section in route i
								for (j1 = 0; j1 < S.items[i].size(); j1++) {
									info.innerI = 0.0;
									info.innerIF = 0.0;
									info.dwellISection = 0.0;
									info.passISection = 0;
									for (j2 = j1; j2 <= S.items[i].size(); j2++) {
										//Keep track of the total costs of the inernal edges of this section of route i (fwd and bkwds)
										if (j2 > j1 + 1) {
											info.innerI += dTime[S.items[i][j2 - 2]][S.items[i][j2 - 1]];
											info.innerIF += dTime[S.items[i][j2 - 1]][S.items[i][j2 - 2]];
										}
										if (j2 > j1) {
											info.dwellISection += calcDwellTime(S.W[i][j2 - 1]);
											info.passISection += S.W[i][j2 - 1];
										}
										if (S.passInRoute[i] - info.passISection + info.passXSection <= maxBusCapacity && S.passInRoute[x] - info.passXSection + info.passISection <= maxBusCapacity) {
											//The proposed move will retain the validity of the route capactities,
											if (j1 == j2) {
												//Inserting a section from route x into route i
												evaluateInsert(newCost, S, i, j1, x, y1, y2, info);
												if (newCost <= bestCost) {
													if (newCost < bestCost) numBest = 0;
													if (rand() % (numBest + 1) == 0) {
														//Save the move with a certain probability
														chosenMove = 2;
														bestCost = newCost; besti = i; bestj1 = j1; bestj2 = j2; bestx = x; besty1 = y1; besty2 = y2; bestflippedx = info.flippedX; bestflippedi = info.flippedI;
													}
													numBest++;
												}
											}
											else {
												//Swapping a section from route x and a section of route i
												evaluateInter(newCost, S, i, j1, j2, x, y1, y2, info);
												if (newCost <= bestCost) {
													if (newCost < bestCost) numBest = 0;
													if (rand() % (numBest + 1) == 0) {
														//Save the move with a certain probability
														chosenMove = 3;
														bestCost = newCost; besti = i; bestj1 = j1; bestj2 = j2; bestx = x; besty1 = y1; besty2 = y2; bestflippedx = info.flippedX; bestflippedi = info.flippedI;
													}
													numBest++;
												}
											}
											evalFeasCnt++;
										}
										evalCnt++;
									}
								}
							}
						}
					}
				}
			}
			/*Inter-route operator that seeks to increase the number of multi-stops by copying stop v = S[i][j1] into route x at
			the best position, where x != i. Route x may already contain v, or may also be empty, but v should have at least 2 boarding
			passengers, and route x should have some spare capacity*/
			for (i = 0; i < S.items.size(); i++) {
				for (j1 = 0; j1 < S.items[i].size(); j1++) {
					if (i != x) {
						if (S.W[i][j1] > 1 && maxBusCapacity - S.passInRoute[x] >= 1) {
							evaluateVertexCopy(newCost, S, i, j1, x);
							if (newCost <= bestCost) {
								if (newCost < bestCost) numBest = 0;
								if (rand() % (numBest + 1) == 0) {
									//Save the move with a certain probability
									chosenMove = 7;
									bestCost = newCost; besti = i; bestj1 = j1; bestx = x;
								}
								numBest++;
							}
						}
					}
				}
			}
			//Now look at the inter-route operators
			if (!S.items[x].empty()) {
				for (y1 = 0; y1 < S.items[x].size(); y1++) {
					info.innerX = 0.0;
					info.innerXF = 0.0;
					for (y2 = y1; y2 < S.items[x].size(); y2++) {
						if (y1 < y2) {
							//Keep track of the total cost of the inernal edges of the section we are considering
							info.innerX += dTime[S.items[x][y2 - 1]][S.items[x][y2]];
							info.innerXF += dTime[S.items[x][y2]][S.items[x][y2 - 1]];
							//Now check the cost of swap
							evaluateSwapTwoOpt(newCost, S, x, y1, y2, 4, info);
							if (newCost <= bestCost) {
								if (newCost < bestCost) numBest = 0;
								if (rand() % (numBest + 1) == 0) {
									//Save the move with a certain probability
									chosenMove = 4;
									bestCost = newCost; bestx = x; besty1 = y1; besty2 = y2;
								}
								numBest++;
							}
							//And the cost of an inversion 
							evaluateSwapTwoOpt(newCost, S, x, y1, y2, 5, info);
							if (newCost <= bestCost) {
								if (newCost < bestCost) numBest = 0;
								if (rand() % (numBest + 1) == 0) {
									//Save the move with a certain probability
									chosenMove = 5;
									bestCost = newCost; bestx = x; besty1 = y1; besty2 = y2;
								}
								numBest++;
							}
						}
						//Now check cost of inserting section (y1,...y2) before point z
						for (z = 0; z <= S.items[x].size(); z++) {
							if (z == y1)
								z = y2 + 1;
							else {
								evaluateOrOpt(newCost, S, x, y1, y2, z, info);
								if (newCost <= bestCost) {
									if (newCost < bestCost) numBest = 0;
									if (rand() % (numBest + 1) == 0) {
										//Save the move with a certain probability
										chosenMove = 6;
										bestCost = newCost; bestx = x; besty1 = y1; besty2 = y2; bestz = z; bestflippedx = info.flippedX;
									}
									numBest++;
								}
							}
						}
					}
				}
			}
		}
		//All neighbourhoods evaluated. We now do the neighbourhood move. First, if no improvement has been found, end. 
		if (chosenMove == 0 || bestCost >= S.cost) {
			break;
		}
		//Otherwise, do the chosen move and repeat.
		if (chosenMove == 1)		doMove1(S, bestx, besty1, besty2, besti, bestCost, bestflippedx);
		else if (chosenMove == 2)	doMove2(S, bestx, besty1, besty2, besti, bestj1, bestCost, bestflippedx);
		else if (chosenMove == 3)	doMove3(S, bestx, besty1, besty2, besti, bestj1, bestj2, bestCost, bestflippedx, bestflippedi);
		else if (chosenMove == 4)	doMove4(S, bestx, besty1, besty2, bestCost);
		else if (chosenMove == 5) 	doMove5(S, bestx, besty1, besty2, bestCost);
		else if (chosenMove == 6)	doMove6(S, bestx, besty1, besty2, bestz, bestCost, bestflippedx);
		else if (chosenMove == 7)	doMove7(S, bestx, besti, bestj1, bestCost);
		numMoves++;
	}

	//We have finished the optimisation procedure
	if (evalCnt > 0) feasRatio = evalFeasCnt / double(evalCnt);
	else feasRatio = 0.0;
	
	if (S.numFeasibleRoutes >= S.items.size()) return true;
	else return false;
}




extern vector<STOP> stops;
extern vector<ADDR> addresses;
extern vector<bool> isOutlier;
extern vector<vector<double> > dDist;
extern vector<vector<double> > dTime;
extern vector<vector<double> > wDist;
extern vector<vector<double> > wTime;
extern vector<vector<int> > stopAdjList;
extern vector<vector<int> > addrAdjList;
extern vector<vector<bool> > addrStopAdj;
extern int totalPassengers, maxBusCapacity;
extern double maxWalkDist;
extern double minEligibilityDist;
extern string distUnits;
extern double dwellPerPassenger;
extern double dwellPerStop;
extern double excessWeight;
extern double maxJourneyTime;
extern bool useMinCoverings;
extern double discreteLevel;
extern int verbosity;
extern vector<int> stopsToPack;
extern vector<int> weightOfStopsToPack;
vector<int> tVec, tVec2;

bool compareSlns(const SOL &lhs, const SOL &rhs) {
	return lhs.costWalk < rhs.costWalk;
}

void printDetails(list<SOL> &A, list<bool> &L, int its) {
	list<bool>::iterator it;
	list<SOL>::iterator AIt;
	int numVisited = 0, numFeas = 0, numInFront = A.size();
	AIt = A.begin();
	for (it = L.begin(); it != L.end(); ++it) {
		if (*it == true)
			numVisited++;
		if ((*AIt).numFeasibleRoutes == (*AIt).items.size()) {
			//Solution is feasible
			numFeas++;
		}
		++AIt;
	}
	cout << its << ") Archive size |A| =  " << numInFront << ", num visited solutions = " << numVisited << ". " << numFeas << " of these are feasible" << endl;
}

bool chooseUnvisitedSolution(list<SOL> &A, list<bool> &visited, SOL &S) {
	//Randomly chooses a member of the archive that has not yet been visited
	list<SOL>::iterator AIt, AChosen;
	list<bool>::iterator vIt, vChosen;
	vIt = visited.begin();
	AIt = A.begin();
	int numChoices = 0;
	while (vIt != visited.end()) {
		if (*vIt == false) {
			if (rand() % (numChoices + 1) == 0) {
				vChosen = vIt;
				AChosen = AIt;
			}
			numChoices++;
		}
		++AIt;
		++vIt;
	}
	if (numChoices == 0) {
		//No solutions are unvisited 
		return false;
	}
	else {
		//Return a random unvisited solution 
		*vChosen = true;
		S = *AChosen;
		return true;
	}
}
	
void updateA(list<SOL> &A, list<bool> &visited, SOL &S) {
	//Procedure that updates a mutually non-dominating archive A with a solution S
	list<SOL>::iterator AIt;
	list<bool>::iterator vIt;
	double k = double(S.items.size());
	double s = double(totalPassengers);
	double base = discreteLevel;
	AIt = A.begin();
	vIt = visited.begin();
	while (AIt != A.end()) {
		if (
			(
				S.cost / k <= (*AIt).cost / k
				&& 
				S.costWalk / s < (*AIt).costWalk / s
			)
			||
			(
				S.cost / k < (*AIt).cost / k
				&&
				S.costWalk / s <= (*AIt).costWalk / s
			)
			) {
			//S strictly dominates the solution (*AIt) in the archive, so delete (*AIt)
			AIt = A.erase(AIt);
			vIt = visited.erase(vIt);
		}
		else if (
			roundDown(S.cost / k, base) >= roundDown((*AIt).cost / k, base)
			&&
			roundDown(S.costWalk / s, base) >= roundDown((*AIt).costWalk / s, base)
			) {
			//S is dominated by a solution in A, so we will not add it, and can end now
			return;
		}
		else {
			++AIt;
			++vIt;
		}
	}
	//If we are here, then we must add S to A because it is mutually non dominating and sufficiently 
	//different with all slns remaining in A
	A.push_back(S);
	visited.push_back(false);
}

void calcSavingWhenAddingAStop(SOL &S, int v, double &saving, bool &addingStop) {
	//Calculate the savings in walking distance (if any) when adding bus stop v to solution S
	saving = 0;
	int j, addr;
	for (j = 0; j < stopAdjList[v].size(); j++) {
		addr = stopAdjList[v][j];
		if (wTime[addr][v] < wTime[addr][S.assignedTo[addr]]) {
			//Addr is closer to v than its current stop, so a saving can be made for all passengers at this address
			saving += (wTime[addr][S.assignedTo[addr]] - wTime[addr][v]) * addresses[addr].numPass;
		}
	}
	if (saving > 0) addingStop = true;
	else			addingStop = false; //Adding the stop makes no difference to peoples' walks
}

void addStop(int v, SOL &S, double saving) {
	int i, j, u, x, r, c, addr;
	//We are going to add a new stop v. First, we need to remove relevant passengers from their current stops and assign them to v
	for (j = 0; j < stopAdjList[v].size(); j++) {
		//Look at each address "addr" adjacent to v and consider the stop u it is currently assigned to
		addr = stopAdjList[v][j];
		u = S.assignedTo[addr];
		if (wTime[addr][v] < wTime[addr][u]) {
			//Addr is closer to v than u so a saving can be made. We do this by removing the x passengers of "addr" from occurences of u in S.W
			x = addresses[addr].numPass;
			S.numBoarding[v] += x;
			S.numBoarding[u] -= x;
			S.assignedTo[addr] = v;
			for (i = 0; i < S.routeOfStop[u].size(); i++) {
				r = S.routeOfStop[u][i];
				c = S.posInRoute[u][r];
				if (S.W[r][c] >= x) {
					S.W[r][c] -= x;
					break;
				}
				else {
					x -= S.W[r][c];
					S.W[r][c] = 0;
				}
			}
		}
	}
	//Now delete bus stops from S.items and S.W for which S.W[i][j] = 0 (if indeed there are any)
	//and recalculate the number of passengers in each route.
	for (i = 0; i < S.W.size(); i++) {
		S.passInRoute[i] = 0;
		j = 0;
		while (j < S.W[i].size()) {
			if (S.W[i][j] == 0) {
				S.W[i].erase(S.W[i].begin() + j);
				S.items[i].erase(S.items[i].begin() + j);
			}
			else {
				S.passInRoute[i] += S.W[i][j];
				j++;
			}
		}
	}
	//Now use BPP style procedure to pack stop v into the solution.
	binPacker(S.items, S.W, S.passInRoute, v, S.numBoarding[v]);
	//Having added v to the solution we now recalculate the auxiliary structures
	repopulateAuxiliaries(S);
	//and, update the costs
	S.cost = calcSolCostFromScratch(S);
	S.costWalk -= saving;
}

void calcSavingWhenRemovingAStop(SOL &S, int v, double &saving, bool doRepair, bool &deletingStop) {
	//Calculate the "savings" (which could be negative) of removing the non-compulsory stop v
	int i, j, addr, u, x, y;
	saving = 0;
	if (doRepair) {
		tVec.clear(); //Keeps a record of additional stops that are added (if any)
		tVec2.clear(); //This keeps a record of how the assignedTo array changes when we repair
	}
	for (i = 0; i < stopAdjList[v].size(); i++) {
		addr = stopAdjList[v][i];
		if (S.assignedTo[addr] == v) {
			//Addr is currently assigned to v, so we need to find another stop u for it (the closest used stop)
			for (j = 0; j < addrAdjList[addr].size(); j++) {
				u = addrAdjList[addr][j];
				if (S.stopUsed[u] && u != v) break; //Addr can be assigned to a stop u != v that is currently being used 
			}
			if (j >= addrAdjList[addr].size()) {
				//An additional stop is required for addr. Either find one, or end
				if (!doRepair) {
					deletingStop = false;
					return;
				}
				//No used stop is suitable for addr, so we assign addr to the closest unused stop u != v instead
				u = addrAdjList[addr][0];
				if (u == v) u = addrAdjList[addr][1];
				tVec.push_back(u);
				S.stopUsed[u] = true;
				tVec2.push_back(addr);
				tVec2.push_back(v);
				S.assignedTo[addr] = u;
				saving += wTime[addr][v] * addresses[addr].numPass;
				saving -= wTime[addr][u] * addresses[addr].numPass;
				//We also need to check if the addition of u affects the walking distances from any other adjacent addresses
				for (j = 0; j < stopAdjList[u].size(); j++) {
					//Check if address x, which is currently assigned to stop y, is closer to stop u
					x = stopAdjList[u][j];
					y = S.assignedTo[x];
					if (x != addr && y != v && wTime[x][u] < wTime[x][y]) {
						tVec2.push_back(x);
						tVec2.push_back(y);
						S.assignedTo[x] = u;
						saving += wTime[x][y] * addresses[x].numPass;
						saving -= wTime[x][u] * addresses[x].numPass;
					}	
				}
			}
			else {
				//Addr has been reassigned to the existing stop u, so the change in walking distance is easy
				if (doRepair) {
					tVec2.push_back(addr);
					tVec2.push_back(v);
					S.assignedTo[addr] = u;
				}
				saving += wTime[addr][v] * addresses[addr].numPass;
				saving -= wTime[addr][u] * addresses[addr].numPass;
			}		
		}
	}
	//If doing repair we now need to to reset the S.stopUsed and S.assignedTo arrays
	if (doRepair) {
		for (i = 0; i < tVec.size(); i++) {
			S.stopUsed[tVec[i]] = false;
		}
		i = tVec2.size() - 1;
		while (i > 0) {
			S.assignedTo[tVec2[i - 1]] = tVec2[i];
			i -= 2;
		}
	}
	deletingStop = true;
}

void removeStop(int v, SOL &S, double saving, bool doRepair) {
	//Remove the non-compulsory used stop v and reassign affected passengers to other stops.
	int i, j, r, c, addr, u, k = S.items.size(), min, x, y;
	//First remove passengers from stop v in the solution
	S.stopUsed[v] = false;
	S.numBoarding[v] = 0;
	for (i = 0; i < S.routeOfStop[v].size(); i++) {
		r = S.routeOfStop[v][i];
		c = S.posInRoute[v][r];
		S.passInRoute[r] -= S.W[r][c];
		S.W[r][c] = 0;
	}
	//Now assign passengers who were boarding v to other stops suitable stops u (this may involve adding new stops).
	for (i = 0; i < stopAdjList[v].size(); i++) {
		addr = stopAdjList[v][i];
		if (S.assignedTo[addr] == v) {
			for (j = 0; j < addrAdjList[addr].size(); j++) {
				u = addrAdjList[addr][j];
				if (S.stopUsed[u] && u != v) break;	//Addr can be assigned to a stop u != v that is currently being used 
			}
			if (j >= addrAdjList[addr].size()) {
				//No used stop is suitable for addr, so we assign addr to the closest unused stop u != v instead
				if (!doRepair) { cout << "Should not be here\n"; exit(1); }
				u = addrAdjList[addr][0];
				if (u == v) u = addrAdjList[addr][1];
				S.stopUsed[u] = true;
				S.assignedTo[addr] = u;
				S.numBoarding[u] = addresses[addr].numPass;
				//We now add stop u to the end of the emtiest route r (we do this now rather than let the BPP heuristic
				//sort it out later, because we might also want to use u again in a bit)
				min = S.passInRoute[0];
				r = 0;
				for (j = 1; j < k; j++) {
					if (S.passInRoute[j] < min) {
						min = S.passInRoute[j];
						r = j;
					}
				}				
				S.items[r].push_back(u);
				S.W[r].push_back(addresses[addr].numPass);
				S.passInRoute[r] += addresses[addr].numPass;
				S.routeOfStop[u].push_back(r);
				S.posInRoute[u][r] = S.items[r].size() - 1;
				//We now need to check if the addition of u affects the walking distances from any other adjacent addresses
				for (j = 0; j < stopAdjList[u].size(); j++) {
					//Check if address x, which is currently assigned to stop y, is actually closer to stop u
					x = stopAdjList[u][j];
					y = S.assignedTo[x];
					if (x != addr && y != v && wTime[x][u] < wTime[x][y]) {
						//Add passengers of address x to stop u
						S.assignedTo[x] = u;
						S.numBoarding[u] += addresses[x].numPass;
						S.W[r].back() += addresses[x].numPass;
						S.passInRoute[r] += addresses[x].numPass;
						//And remove them from stop y
						S.numBoarding[y] -= addresses[x].numPass;
						eliminateFromW(S, y, addresses[x].numPass);
					}
				}
			}
			else {
				//Addr has been reassigned to the existing stop u, so add it to the emptiest route containing u
				r = S.routeOfStop[u][0];
				min = S.passInRoute[r];
				for (j = 1; j < S.routeOfStop[u].size(); j++) {
					if (S.passInRoute[S.routeOfStop[u][j]] < min) {
						min = S.passInRoute[S.routeOfStop[u][j]];
						r = S.routeOfStop[u][j];
					}
				}
				c = S.posInRoute[u][r];
				S.W[r][c] += addresses[addr].numPass;
				S.passInRoute[r] += addresses[addr].numPass;
				S.assignedTo[addr] = u;
				S.numBoarding[u] += addresses[addr].numPass;
			}
		}
	}
	//Now delete all instances of where S.W = 0. This may mean that some stops that were previously being used may now not be.
	//tVec keeps track of how many instatnces of each stop are deleted. If all of them are, the stop is no longer used
	tVec.clear();
	tVec.resize(stops.size(), 0); 
	for (i = 0; i < S.W.size(); i++) {
		j = 0;
		while (j < S.W[i].size()) {
			if (S.W[i][j] == 0) {
				u = S.items[i][j];
				tVec[u]++;
				if (tVec[u] == S.routeOfStop[u].size()) {
					S.stopUsed[u] = false; //We are no longer using stop u in the solution
				}
				S.W[i].erase(S.W[i].begin() + j);
				S.items[i].erase(S.items[i].begin() + j);
			}
			else {
				j++;
			}
		}
	}
	//At this point, some routes may be overfull, so delete randomly chosen stops from each one
	stopsToPack.clear();
	weightOfStopsToPack.clear();
	for (i = 0; i < k; i++) {
		while (S.passInRoute[i] > maxBusCapacity) {
			j = rand() % (S.items[i].size());
			stopsToPack.push_back(S.items[i][j]);
			weightOfStopsToPack.push_back(S.W[i][j]);
			S.passInRoute[i] -= S.W[i][j];
			S.items[i].erase(S.items[i].begin() + j);
			S.W[i].erase(S.W[i].begin() + j);
		}
	}
	//Use BPP style procedure to pack all the children on to k buses.
	binPacker(S.items, S.W, S.passInRoute, stopsToPack, weightOfStopsToPack);

	//Finally, we need to repopulate the residual structures. 
	repopulateAuxiliaries(S);

	//...and calculate the costs
	S.cost = calcSolCostFromScratch(S);
	S.costWalk = S.costWalk - saving;
}

void doMultiObjOptimisation(list <SOL> &A) {
	
	//This takes an archive of solution(s) and runs the mobj process
	list<bool> visited;
	list<bool>::iterator vIt;
	list<SOL>::iterator AIt;
	int v, its = 1, numMoves, k = A.front().items.size();
	double saving, feasRatio;
	bool addingStop, deletingStop;
	SOL S, SPrime;
	
	//Mark the initial solution in the archive as unvisited
	visited.push_back(false);

	//Also add the solution where all students are given the shortest possible walk
	makeInitSol(S, k, 3);
	localSearch(S, feasRatio, numMoves);
	updateA(A, visited, S);
		
	if (verbosity >= 1) 
		cout << "\n\nNow using multiobjective techiniques to produce a range of solutions that use " << k << " buses.\n\n";
	
	while (true) {

		//Select a non-visited member S of the archive. If all are visited, end the algorithm.
		if (verbosity >= 1) {
			printDetails(A, visited, its);
		}
		if (chooseUnvisitedSolution(A, visited, S) == false) {
			break;
		}
					
		//If we are here, S is now a solution we will be visiting from (and has therefore been marked as visited)
		for (v = 1; v < stops.size(); v++) {
			if (!S.stopUsed[v]) {
				//Explore consequences of adding the currently unusued stop v
				calcSavingWhenAddingAStop(S, v, saving, addingStop);
				if (addingStop) {
					SPrime = S;
					addStop(v, SPrime, saving);
					localSearch(SPrime, feasRatio, numMoves);
					updateA(A, visited, SPrime);
				}
			}
			else {
				if (!stops[v].required) {
					//Explore consequences of removing stop the currently used, non-compulsory stop v
					calcSavingWhenRemovingAStop(S, v, saving, true, deletingStop);
					if (deletingStop) {
						SPrime = S;
						removeStop(v, SPrime, saving, true);
						localSearch(SPrime, feasRatio, numMoves);
						updateA(A, visited, SPrime);
					}
				}
			}
		}
		its++;
	}
	//Now sort the front and end
	A.sort(compareSlns);
}


//Global variables
vector<STOP> stops;
vector<ADDR> addresses;
vector<bool> isOutlier;
vector<vector<double> > dDist;
vector<vector<double> > dTime;
vector<vector<double> > wDist;
vector<vector<double> > wTime;
vector<vector<int> > stopAdjList; //Gives a list of addresses adjacent to each stop
vector<vector<int> > addrAdjList; //Gives a list of stops adjacent to each address
vector<vector<bool> > addrStopAdj;
int totalPassengers, maxBusCapacity, kInit, timePerK;
string distUnits;
double maxWalkDist;
double minEligibilityDist;
// double dwellPerPassenger;
// double dwellPerStop;
// double excessWeight;
// double maxJourneyTime;
double discreteLevel;
int verbosity;
bool useMinCoverings;

void printSln(SOL &S) {
	//Writes details of a particular solution to the screen
	int i, j, k = S.items.size();
	bool containsOutlier = false;
	cout << "****************SOLUTION******************************\n";
	cout << "Number of buses = " << S.items.size() <<"\n"
		<< "Average walk time per person = " << (S.costWalk / double(totalPassengers)) / 60.0 << " mins.\n"		
		<< "Average route length = " << (sumDouble(S.routeLen) / double(k)) / 60.0 << " mins.\n"
		<< "The bus stops visited in each route, in order, are as follows:\n";
	for (i = 0; i < k; i++) {
		cout << "Route" << setw(3) << i << " (" << setw(3) << int(ceil(S.routeLen[i] / 60.0)) << " mins) = ( ";
		for (j = 0; j < S.items[i].size(); j++) {
			if (isOutlier[S.items[i][j]]) {
				cout << S.items[i][j] << "* ";
				containsOutlier = true;
			}
			else cout << S.items[i][j] << " ";
		}
		cout << ")\n";
	}
	if (containsOutlier) cout << "Outlier bus stops (compulsory bus stops more than m_t mins from the school) are marked with an *s.\n";
	cout << "The address -> bus stop assignments, in order, are as follows:\n{ ";
	for (i = 0; i < addresses.size(); i++) {
		cout << "(" << i << "," << S.assignedTo[i] << ") ";
	}
	cout << "}\n";
	cout << "******************************************************\n\n";
}

ostream& printSln(ostream &os, SOL &S) {
  int i, j, k = S.items.size();
  bool containsOutlier = false;
  os << S.items.size() << "\n";
  for (i = 0; i < k; i++) {
    os << S.items[i].size() << " ";
    for (j = 0; j < S.items[i].size(); j++) {
      os << S.items[i][j] << " " << S.W[i][j] << " ";
    }
    os << "\n";
  }
  for (i = 0; i < addresses.size(); i++) {
    os << S.assignedTo[i] << " ";
  }
  return os;
}

SOL ILS(int k, bool &foundFeas) {
	//The ILS algorithm for producing a solution using k buses.
	bool feasible = false;
	foundFeas = false;
	int i = 1;
	SOL S, bestS;
	double feasRatio;
	clock_t endTime;
	int numMoves, stopsDeleted, maxIts;
	//Decide if we're running the procedure to a time limit or iteration limit
	if (timePerK >= 0) {
		endTime = clock() + timePerK * CLOCKS_PER_SEC;
		maxIts = 0;
	}
	else {
		endTime = 0;
		maxIts = timePerK * -1;
	}
	//Produce an inital solution and move to a minimum
	makeInitSol(S, k, 1);
	feasible = localSearch(S, feasRatio, numMoves);
	if (feasible && !foundFeas) {
		//Feasibility has been found for the first time,
		foundFeas = true;
	}
	bestS = S;
	if (verbosity >= 2) {
		cout << "\n  k      it        Cost  #Feas #Empty       #Stops    StopsDel  MovesToMin    BestCost\n";
		cout << "-------------------------------------------------------------------------------------------------\n";
		cout << setw(3) << k << setw(8) << i << setw(12) << S.cost << setw(7) << S.numFeasibleRoutes << setw(7) << S.numEmptyRoutes << setw(10) << S.solSize << "/" << S.numUsedStops << setw(12) << "-" << setw(12) << numMoves << setw(12) << bestS.cost << "\n";
	}
	while(clock() < endTime || i <= maxIts) {
		//Peturb the solution and move to the minimum
		stopsDeleted = makeNewCovering(S);
		feasible = localSearch(S, feasRatio, numMoves);
		i++;
		if (feasible && !foundFeas) {
			//Feasibility has been found for the first time, so record the solution
			foundFeas = true;
			bestS = S;
		}
		else if (feasible && S.cost < bestS.cost) {
			//A new feasible solution has been found with an even better cost, so record it 
			bestS = S;
		}
		else if (!feasible && !foundFeas && S.cost < bestS.cost) {
			//Feasibility has not yet been found, but we have found a better infeasible solution so record it
			bestS = S;
		}
		//Note, we do not accept a new infeasible solution that has a better cost than a previously oberved feasible solution
		if (verbosity >= 2) {
			cout << setw(3) << k << setw(8) << i << setw(12) << S.cost << setw(7) << S.numFeasibleRoutes << setw(7) << S.numEmptyRoutes << setw(10) << S.solSize << "/" << S.numUsedStops << setw(12) << stopsDeleted << setw(12) << numMoves << setw(12) << bestS.cost << "\n";
		}
	}
	return bestS;
}


//Info output if different no parameters used
void usage() {
	cout << "School Bus Optimiser\n";
	cout << "--------------------\n";
	cout << "USAGE:\n"
		<< "---- Compulsory -------------------------------------------\n"
		<< "-i  <inFileName>         (must be a .bus file in the correct format. Do not include extension)\n"
		<< "---- Optional ---------------------------------------------\n"
		<< "-m  <double>             (Maximum bus journey time in minutes. Default = 45.0)\n"
		<< "-c                       (Maximum bus capacity. Default = 70)\n"
		<< "-t  <int>                (CPU time limit per-k in seconds. Default = 10. If negative value used, defines number of calls to LS (iterations) per k instead.)\n"
		<< "-D  <double>             (Discrete level. Minimum number of secs between each solution in the Pareto front. Larger values make runs faster but less accurate. Default = 10.0)\n"
		<< "-M                       (If present, bus stop subsets in Stage-1 must be minimal set coverings; else not.)\n"
		<< "-S                       (If present, only Stage 1 of the algorithm is run.)\n"
		<< "------------\n"
		<< "-d  <double> <double>    (Dwell time coefficients, seconds-per-passenger and seconds-per-stop resp. Defaults = 5.0 and 15.0)\n"
		<< "-r  <int>                (Random seed. Default = 1)\n"
		<< "-k  <int>                (Number of buses k to start at. Default is the lower bound (numStudents divided by busCapacity, rounded up to nearest integer)\n"
		<< "-v                       (Verbosity. Repeat for more output to the screen)\n"
		<< "------------------------------------------------------------\n";
	exit(0);
}

int main(int argc, char *argv[]){

	// if(argc <=1){
	// 	usage();
	// 	exit(1);
	// }

	//Determine run variables and set default values
	int i, totalTime, k = -1, seed = 1;
	string infile;
	bool foundFeas;
	verbosity = 0;
	dwellPerPassenger = 5.0;
	discreteLevel = 10.0;
	timePerK = 10;
	dwellPerStop = 15.0;
	maxBusCapacity = 70;
	useMinCoverings = false;
	bool stageOneOnly = false;
	list<SOL> A;
		
	// try {
	// 	//Read in all command line parameters. If there's an error, end immediately.
	// 	for (i = 1; i < argc; i++) {
	// 		if (strcmp("-r", argv[i]) == 0) {
	// 			seed = atoi(argv[++i]);
	// 		}
	// 		else if (strcmp("-t", argv[i]) == 0) {
	// 			timePerK = atoi(argv[++i]);
	// 		}
	// 		else if (strcmp("-d", argv[i]) == 0) {
	// 			dwellPerPassenger = atof(argv[++i]);
	// 			dwellPerStop = atof(argv[++i]);
	// 		}
	// 		else if (strcmp("-k", argv[i]) == 0) {
	// 			k = atoi(argv[++i]);
	// 		}
	// 		else if (strcmp("-m", argv[i]) == 0) {
	// 			maxJourneyTimeMins = atof(argv[++i]);
	// 		}
	// 		else if (strcmp("-S", argv[i]) == 0) {
	// 			stageOneOnly = true;
	// 		}
	// 		else if (strcmp("-v", argv[i]) == 0) {
	// 			verbosity++;
	// 		}
	// 		else if (strcmp("-c", argv[i]) == 0) {
	// 			maxBusCapacity = atoi(argv[++i]);
	// 		}
	// 		else if (strcmp("-D", argv[i]) == 0) {
	// 			discreteLevel = atof(argv[++i]);
	// 		}
	// 		else if (strcmp("-M", argv[i]) == 0) {
	// 			useMinCoverings = true;
	// 		}
	// 		else if (strcmp("-i", argv[i]) == 0) {
	// 			//read in the problem file (in the .bus format) and construct the relevant arrays.
	// 			infile = argv[++i];
	// 			string infileWithExtension = infile + ".bus";
	// 			readInput(infileWithExtension);
	// 		}
	// 		else {
	// 			cout << "Invalid input statement. ("<< argv[i] <<"). Please try again.\n";
	// 			usage();
	// 			exit(1);
	// 		}
	// 	}
	// }
	// catch (...) {
	// 	cout << "Invalid input statement. Please try again.\n";
	// 	usage();
	// 	exit(1);
	// }
  stageOneOnly = true;

  // ifstream in("0.in");
  readInput(std::cin);

	//Convert max journey time to seconds to be consistent with input files
	maxJourneyTime = maxJourneyTimeMins * 60.0;

	//By default the excess weight is set to the max journey time (in seconds)
	excessWeight = maxJourneyTime;

	//Set seed and start the clock	
	srand(seed);
	time_t startTime, endTime;
	startTime = clock();

	//Determine any bus stops that are outliers (i.e. far from the school) by populating the isOutlier vector
	getOutliers();

	//Determine initial number of buses kInit. This is either the LB or specified by the user 
	kInit = int(ceil(totalPassengers / double(maxBusCapacity)));
	if (k < kInit) k = kInit;

	//Algorithm Stage 1: Find a feasible solution --------------------------------------------------------
	foundFeas = false;
	SOL S;
	while(k <= addresses.size()) {
		if (verbosity >= 1) cout << "\nUsing ILS to find a feasible solution using " << k << " buses:" << endl;
		S = ILS(k, foundFeas);
		if (foundFeas) break;
		else  k++;
	}
	
	//Record how long it took to find a feasible solution and output some info
	endTime = clock();
	int midTime = (int)(((endTime - startTime) / double(CLOCKS_PER_SEC)) * 1000);
	if (verbosity >= 1) {
		cout << "\nILS method completed in " << midTime << " ms\n";
		checkSolutionValidity(S, true);
		if (verbosity >= 2) {
			cout << "\nHere is the best solution found by ILS:\n\n";
			printSln(S);
		}
	}

	if (stageOneOnly == false) {
		//We are now running Stage 2 (the multi-objective part) too. First we Add this single feasible solution to the archive A
		A.push_back(S);
		//Now do the multiobjective optimisation
		doMultiObjOptimisation(A);
		//Stop the clock
		endTime = clock();
		totalTime = (int)(((endTime - startTime) / double(CLOCKS_PER_SEC)) * 1000);
		if (verbosity >= 1) {
			cout << "\nRun completed in " << totalTime << " ms" << endl;
		}
	}
  // ofstream result("result.out");
  // printSln(result, S);
  printSln(std::cout, S);

	return 0;
}

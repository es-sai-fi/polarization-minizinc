include "globals.mzn";

% ---- Constants ----
set of int: k = 1..3;

% ---- Parameters ----
int: n;
int: m;
float: ct;
float: max_movs;
array[1..m] of 0..n: p;
array[1..m, k] of 0..n: s;
array[1..m] of 0.0..1.0: v;

% ---- Variables and domains ----
array[k, 1..m, 1..m] of var 0..n: x;
array[1..m] of var 0..n: p_aux;
var float: polarization;
array[1..m] of var 0..n: acum;
var float: median;
var 1..n: pos_low;
var 1..n: pos_high;
var 1..m: idx_low;
var 1..m: idx_high;

% ---- Constraints ----
% No movements to the same opinion value
constraint forall(k_val in k, i in 1..m) (
  x[k_val, i, i] = 0
);

% There shouldn't be more moved persons with a given k value than the initial
% number of persons with said value
constraint forall(k_val in k, i in 1..m) (
  sum(j in 1..m)(x[k_val, i, j]) <= s[i, k_val]
);

% Number of movements done should be lower or equal to max_movs 
constraint sum(k_val in k, i in 1..m, j in 1..m where i != j)(x[k_val, i, j]) <= max_movs;

% Total cost of movements done should be lower or equal to ct 
constraint sum(k_val in k, i in 1..m, j in 1..m where i != j)(
    x[k_val, i, j] * abs(i - j) * k_val
) <= ct;

% The new distribution vector will be the starting p[j] value plus the sum of
% the moved persons to said opinion value minus the sum of the moved persons
% from that opinion value
constraint forall(j in 1..m) (
  p_aux[j] = p[j] + sum(k_val in k, i in 1..m where i != j)(x[k_val, i, j]) 
              - sum(k_val in k, i in 1..m where i != j)(x[k_val, j, i])
);

% Each distribution should always have the same number of persons
constraint sum(i in 1..m)(p_aux[i]) = n;

% Acum calculation
constraint acum[1] = p_aux[1];
constraint forall(i in 2..m) (
    acum[i] = acum[i-1] + p_aux[i]
);

% Median calculation 
% If n is even then the lower position would be n / 2 (integer division) and the
% higher position would be lower position + 1. If n is not even then both lower
% and higher positions will have the same value
constraint
  if n mod 2 = 0 then
    pos_low = n div 2 /\ pos_high = n div 2 + 1
  else
    pos_low = (n + 1) div 2 /\ pos_high = (n + 1) div 2
  endif;

% idx_low is the first index whose acumulative >= pos_low
constraint acum[idx_low] >= pos_low /\ (idx_low == 1 \/ acum[idx_low - 1] < pos_low);
% idx_high is the first index whose acumulative >= pos_high
constraint acum[idx_high] >= pos_high /\ (idx_high == 1 \/ acum[idx_high - 1] < pos_high);

median = (v[idx_low] + v[idx_high]) / 2.0;

% Polarization calculation
constraint polarization = sum(i in 1..m)(
    p_aux[i] * abs(v[i] - median)
);

% ---- Redundant Constraints ----
% There shouldn't be more moved persons with a given opinion value than the
% initial number persons with said value 
constraint forall(i in 1..m) (
    sum(k_val in k, j in 1..m where i != j)(x[k_val, i, j]) <= p[i]
);

% ---- Solve ----
solve minimize polarization;

% ---- Output ----
output [show(polarization), show(x)];

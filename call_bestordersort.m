%{
 Copyright [2017] [Proteek Chandan Roy]
 icensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at
 http://www.apache.org/licenses/LICENSE-2.0
 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 
 This file is a StandAlone software that implemented non-dominated sorting algorithm of the following paper
 Please cite this paper whenever the code is used.
 Bibtex entry
 @inproceedings{Roy:2016:BOS:2908961.2931684,
	 author = {Roy, Proteek Chandan and Islam, Md. Monirul and Deb, Kalyanmoy},
	 title = {Best Order Sort: A New Algorithm to Non-dominated Sorting for Evolutionary Multi-objective Optimization},
	 booktitle = {Proceedings of the 2016 on Genetic and Evolutionary Computation Conference Companion},
	 series = {GECCO '16 Companion},
	 year = {2016},
	 isbn = {978-1-4503-4323-7},
	 location = {Denver, Colorado, USA},
	 pages = {1113--1120},
	 numpages = {8},
	 url = {http://doi.acm.org/10.1145/2908961.2931684},
	 doi = {10.1145/2908961.2931684},
	 acmid = {2931684},
	 publisher = {ACM},
	 address = {New York, NY, USA},
	 keywords = {best order sort, layers of maxima, maximal vector computation, multi-objective optimization, non-dominated sorting, pareto set, pareto-efficiency, skyline operator, vector sorting},
} 
@author Proteek Chandan Roy, Department of CSE, Michigan State University, USA
Contact: royprote@egr.msu.edu, proteek_buet@yahoo.com
%}



clear java;
debug = false;
print = true;
javaaddpath(fullfile(pwd,'bos.jar'));
method = BestOrderSort;
population = rand(100000,10);
I = method.best_order_sort(population, false, true);
disp(I.time)
disp(I.comparison)


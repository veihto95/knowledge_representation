import timeit
import numpy as np
import re
import heapq
import math
from collections import defaultdict
import pickle

mapping = {'EQ':int(2), 'B':int(4),'BI':int(8),'D':int(16),'DI':int(32), 'O':int(64), 'OI':int(128), 'M':int(256), 'MI':int(512), 'S':int(1024), 'SI':int(2048), 'F':int(4096), 'FI':int(8192)}
priority_mapping = {0:0, 2:1, 4:2, 8:2, 16:3, 32:3, 64:3, 128:3, 256:3, 512:3, 1024:3, 2048:3, 4096:3, 8192:3}
nodelist = []

def get_labels_pred():
    with open('labels.pickle', 'rb') as handle:
        labels = pickle.load(handle)
    with open('pred.pickle', 'rb') as handle:
        pred = pickle.load(handle)
    return labels, pred

def intersection(a, b):
    return (a & b)

def union(a, b):
    return (a | b)

def complement(a):
    res = 0
    rev = 0
    for i in [0,1,2]:
        res = mapping[a] & (1<<i)
        if res >= 1:
            rev = rev & ~(1<<i)
        else:
            rev = rev | (1<<i)
    return list(mapping.keys())[list(mapping.values()).index(rev)]
    
def converse(p):
    p = _find_base_relations(p)
    sum = 0
    for base_relation in p:
        sum += converse_table[base_relation]
    return sum

def composition(a, b): 
    if type(a) == int:
        if a == 0:
            return 0
    if type(b) == int:
        if b == 0:
            return 0
    if type(a) == int:
        if a == universe:
            return universe
    if type(b) == int:
        if b == universe:
            return universe
    if type(a) == int:
        a = _find_base_relations(a)
    if type(b) == int:
        b = _find_base_relations(b)
    r = 0
    for i in a:
        for j in b:
            r = union(r, composition_ia[(i, j)])
    return r

def list_base_relations(mapping):
    base_relations = []
    for relation in mapping:
        base_relations.append(mapping[relation])
    return base_relations

def composition_ia_init():
    content = []
    sum = 0
    f = open('composition.txt', "r")
    for line in f:
        values = re.split('[\s()]+', line)
        content.append(values[0:len(values)-1])
    composition_ia = {}
    for i in range(0, len(content)):
        sum = 0
        for k in range(2, len(content[i])):
            sum += mapping[content[i][k]]
        composition_ia[(mapping[content[i][0]], mapping[content[i][1]])] = sum
    return composition_ia

def _atractable():
    queue = []
    f = open('ia_ord_horn.txt', "r")
    for line in f:
        if not '#' in line:
            sum = 0
            values = re.split('[\s()]+', line)
            values = values[0:len(values)-1]
            for i in range(0,len(values)):
                sum += mapping[values[i]]
            heapq.heappush(queue, sum)
    return queue

def atractable_dict():
    dictionary = {}
    for relation in atractable:
        dictionary[relation] = len(_find_base_relations(relation)) 
    return dictionary

def _calculate_sum():
    sum = 0
    for i in mapping.values():
        sum = sum + i
    return sum
  
def _find_base_relations(n):
    binaries = []
    if n in base_relations:
        return [n]
    br_queue = []
    for relation in base_relations:
        heapq.heappush(br_queue, -relation)
    while(n != 0):
        base_relation = (-1)*heapq.heappop(br_queue)
        if base_relation <= n:
            n -= base_relation
            binaries.append(base_relation)
    return binaries

def _count_bits(n): 
    count = 0
    while (n): 
        count += n & 1
        n >>= 1
    return count 

def calculate_priority(n):
    relations = _find_base_relations(n)
    priority = 0
    for i in range(0, len(relations)):
        priority += priority_mapping[relations[i]]
    return priority

def nodes():
    relation_dict = {}
    for relation in base_relations:
        relation_dict[relation] = False
    all_nodes(relation_dict)
    
def all_nodes(relation_dict, run = 0):    
    if run == len(base_relations):
        sum = 0
        for relation in base_relations:
            if relation_dict[relation] == True:
                sum += relation
        #empty relation is unnecessary
        #if sum != 0:
        nodelist.append(sum)
        return
    relation_dict[base_relations[run]] = True
    all_nodes(relation_dict, run + 1)
    relation_dict[base_relations[run]] = False
    all_nodes(relation_dict, run + 1)
    return

def save_obj(mydict, name ):
    with open(name, 'wb') as handle:
        pickle.dump(mydict, handle, protocol = pickle.HIGHEST_PROTOCOL)

def minimal_cover(v):
    green = []
    yellow = []
    heapq.heappush(yellow, [0, v])
    dist = {}
    dist[v] = 0
    pred = {}
    pred[v] = None
    labels = {}
    for vertex in nodelist:
        if vertex != v:
            dist[vertex] = float('inf')
            pred[vertex] = None
    while len(yellow) > 0:
        w = heapq.heappop(yellow)[1]
        green.append(w)
        if yellow == None:
            yellow = []
        for s in atractable:
            if union(w, s) in nodelist:
                if union(w, s) not in green and ((dist[w] + 1) < dist[union(w, s)]):
                    #faerbe die Kante rot
                    labels[(w, union(w, s))] = s
                    dist[union(w, s)] = dist[w] + 1
                    pred[union(w, s)] = w
                    heapq.heappush(yellow, [dist[union(w, s)], union(w, s)])
    save_obj(labels, 'labels.pickle')
    save_obj(pred, 'pred.pickle')
    return labels, pred
                 
def aclosure(size, network):
    queue = []
    for i in range(0, size):
        for j in range(0, size):
            priority = calculate_priority(network[i][j])
            heapq.heappush(queue, [priority, (i, j)])
    while queue != []:
        edge = heapq.heappop(queue)[1]
        i = edge[0]
        j = edge[1]
        if i == j:
            continue
        for k in range(0, size):  
            if k != i and k != j:
                cik = intersection(network[i][k], composition(network[i][j], network[j][k]))
                if cik != network[i][k]:
                    network[i][k] = cik
                    priority = calculate_priority(network[i][k])
                    heapq.heappush(queue, [priority, (i, k)])
                ckj = intersection(network[k][j], composition(network[k][i], network[i][j]))
                if ckj != network[k][j]:
                    network[k][j] = ckj
                    priority = calculate_priority(network[k][j])
                    heapq.heappush(queue, [priority, (k, j)])
    return network    

def aclosure2(size, network, q = None):
    relation_dict = {}
    if q == None:
        q = []    
        priority = 0
        for i in range(0,size):
            for j in range(i+1,size):
                if network[i][j] == 0:
                    return None
                priority = calculate_priority(network[i][j])
                heapq.heappush(q, [priority, (i, j)])
                relation_dict[(i, j)] = priority
    else:
        for i in range(0,size):
            for j in range(0,size):
                if network[i][j] == 0:
                    return None
        for edge in q:
            relation_dict[(edge[1][0], edge[1][1])] = edge[0]
    while len(q) != 0:
        cur_elem = heapq.heappop(q)        
        cur_i = cur_elem[1][0]
        cur_j = cur_elem[1][1]
        relation_dict.pop((cur_i, cur_j), None)
        for k in range(0,size): 
            if k != cur_i and k != cur_j and cur_i != cur_j:
                new_constraint = intersection(network[cur_i][k], composition(network[cur_i][cur_j], network[cur_j][k]))
                if new_constraint == 0:
                    return None
                if new_constraint != network[cur_i][k]:
                    network[cur_i][k] = new_constraint
                    #enqueue new
                    if (cur_i, k) not in relation_dict.keys():
                        priority = calculate_priority(network[cur_i][k])
                        heapq.heappush(q, [priority, (cur_i, k)])
                        relation_dict[(cur_i, k)] = priority        
                new_constraint = intersection(network[k][cur_j], composition(network[k][cur_i], network[cur_i][cur_j]))
                if new_constraint == 0:
                    return None
                if new_constraint != network[k][cur_j]:
                    network[k][cur_j] = new_constraint
                    #enqueue new
                    if (k, cur_j) not in relation_dict.keys():
                        priority = calculate_priority(network[k][cur_j])
                        heapq.heappush(q, [priority, (k, cur_j)])
                        relation_dict[(k, cur_j)] = priority
    return network

def refinement_search_1(size, matrix):
    network_ref = [row[:] for row in matrix]
    new_network = aclosure(size, network_ref)
    for i in range(0, size):
        for j in range(0, size):
            if new_network[i][j] == 0:
                return False
    base_only = True
    cur_edge = None
    for i in range(0, size):
        for j in range(i+1, size):
            if new_network[i][j] not in mapping.values():
                cur_edge = (i, j)
                base_only = False
                break
        if base_only == False:
            break
    if base_only == True: 
        return True
    i = cur_edge[0]
    j = cur_edge[1]
    relations = _find_base_relations(new_network[i][j])
    network_ref = new_network
    for z in range(0, len(relations)):            
        new_network[i][j] = relations[z]
        new_network[j][i] = converse_table[relations[z]]        
        if refinement_search_1(size, new_network) == True:
            return True
    return False

def refinement_search_15(size, matrix, edge = None):
    refine_queue = []
    network_ref = [row[:] for row in matrix]
    new_network = aclosure2(size, network_ref, edge)
    if new_network == None:
        return False
    base_only = True
    for i in range(0, size):
        for j in range(i+1, size):
            if new_network[i][j] not in base_relations:
                refine_queue.append((i, j))
                base_only = False
    if base_only == True:
        return True
    edge = heapq.heappop(refine_queue)
    i = edge[0]
    j = edge[1]
    relations = _find_base_relations(new_network[i][j])
    for z in range(0, len(relations)):            
        new_network[i][j] = relations[z]
        new_network[j][i] = converse(relations[z])
        if refinement_search_15(size, new_network, [[1, (i, j)]]) == True:
            return True
    return False

def refinement_lookup():
    labels, pred = get_labels_pred()
    refinement_lookup = {}
    for node in nodelist:
        n = node
        refinement_lookup[n] = []
        refinement_queue = []
        while pred[node] != None:
            priority = calculate_priority(labels[(pred[node], node)])
            heapq.heappush(refinement_queue, [-priority, labels[(pred[node], node)]])
            node = pred[node]
        while refinement_queue != []:
            next_constraint = heapq.heappop(refinement_queue)[1]
            refinement_lookup[n].append(next_constraint)          
    return refinement_lookup

def refinement_search_15_plus(size, matrix, edge = None):
    refine_queue = []
    network_ref = [row[:] for row in matrix]
    new_network = aclosure2(size, network_ref, edge)
    if new_network == None:
        return False
    is_atractable = True
    for i in range(0, size):
        for j in range(i+1, size):
            if new_network[i][j] not in atractable:
                priority = calculate_priority(new_network[i][j])
                heapq.heappush(refine_queue, [priority, (i, j)])
                is_atractable = False
    if is_atractable == True:
        return True
    #select most constraining relation
    edge = heapq.heappop(refine_queue)
    i = edge[1][0]
    j = edge[1][1]
    #select least constraining tractable relation
    relations = refinement_lookup[new_network[i][j]]
    for z in range(0, len(relations)):            
        new_network[i][j] = relations[z]
        new_network[j][i] = converse(relations[z])
        if refinement_search_15_plus(size, new_network, [[1, (i, j)]]) == True:
            return True
    return False

#Initialization and parsing
f = open('ia_test_instances_10b.txt', "r")
conv = open('ia_converses.txt', "r")
content = []
qcsp = []
base_relations = list_base_relations(mapping)
atractable = _atractable()
atractable_dict = atractable_dict()
universe = _calculate_sum()
composition_ia = []
converse_table = {}
for line in conv:
    pair = line.split()
    converse_table[mapping[pair[0]]] = mapping[pair[1]]
for line in f:   
    if "." in line:
        qcsp.append(content)
        content = []
    elif not "#" in line:
        values = re.split('[\s()]+', line)
        content.append(values[0:len(values)-1])
maxidx = 0
matrix = [[]]
composition_ia = composition_ia_init()
nodes()
refinement_lookup = refinement_lookup()
idx = 0
for task in qcsp:
    idx += 1
    for i in range(0,len(task)):
        if max(int(task[i][0]),int(task[i][1])) > maxidx:
            maxidx = max(int(task[i][0]),int(task[i][1]))
    matrix = [[universe for x in range(maxidx+1)] for y in range(maxidx+1)]
    for i in range(0,len(task)):
        sum = 0
        for j in range(2, len(task[i])):
            sum = sum + mapping[task[i][j]]
        current_node = matrix[int(task[i][0])][int(task[i][1])]        
        matrix[int(task[i][0])][int(task[i][1])] = intersection(matrix[int(task[i][0])][int(task[i][1])], sum)
        matrix[int(task[i][1])][int(task[i][0])] = converse(matrix[int(task[i][0])][int(task[i][1])])
    res = refinement_search_15_plus(len(matrix), matrix)
    if res == False:
        print(idx, 'FINAL: network inconsistent')
    else:
        print(idx, 'FINAL: network consistent')



    
    

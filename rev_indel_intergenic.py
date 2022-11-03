# encoding: utf-8

import math
import sys
import random
import itertools
import time


DEBUG = False


#####################################################################
################## REPRESENTS A NODE OF A GRAPH #####################
#####################################################################

class cycle_graph_node :

    def __init__(self, index, padded) :
        #index  : stores the black edge i, 0 <= i <= n+1
        #value  : stores pi_i
        self.index, self.value    = index, 0        
        self.padded   = padded
        self.cycle    = 0
        ## Kind:
        ## 0 = unset
        ## 1 = small cycle             (1)
        ## 2 = oriented    convergent  (3, 1, 2)
        ## 3 = even        convergent  (2,  1)
        ## 4 = even        divergent   (2, -1)
        ## 5 = nonoriented convergent  (3, 2, 1)
        ## 6 = oriented    divergent   (3,-2,-1), (3,1,-2), (3,-1, 2)
        ## 7 = nonoriened  divergent   (3,2,-1),  (3,-2,1), (3,-1,-2)
        self.kind     = 0

        ## 0 = unset 
        ## i = num of black edges
        self.size        = 0 

        ## 0   = unset or balanced
        ## +-i = (gray - black) weights
        self.blacks      = 0
        self.grays       = 0
        self.gray_labeled     = False
        self.black_labeled    = False

        ## 0 = unset
        ## 1 = convergent
        ## 2 = divergent
        self.direction = 0

        #ap     : points to the record that stores pi_{i-1}, 1 <= i <= n+1
        #ab     : points to the record that stores pi_{i+1}, 0 <= i <= n
        #ac     : points to the record that stores i + 1,    0 <= i <= n
        self.ap, self.ab, self.ac = 0,0,0

        #visit  : indicates if the record has been visited
        self.visit  = False

        ## when gray or black edges are labeled, we will list the
        ## sizes of all intergenic regions between them. if the
        ## len(wc) = lc + 1 and len(wp) = lp + 1
        self.wc                   = [0,]
        self.wp                   = [0,]
        self.wcs                  = 0
        self.wps                  = 0
        self.lc                   = 0
        self.lc_iota              = []
        self.lp                   = 0

############################################################################
############ Do not need to represent a real permutation ###################
############################################################################

## This class represents an unoriented cycle-graph. Keep in mind that
## this class is not the same as used for the sorting by transposition
## problem. Here, the white edges are not the reverse of the black
## edges as before. That is because the black edges can go from righ
## to left as well as to left to right.

## For instance, assume a permutation (5, 2, ...). The configuration
## in the graph would be.

## node(0).ap  = -5      ## node(0).ab  = Null
## node(-5).ab = 5       ## node(-5).ap = 0  
## node(5).ap  = -2      ## node(5).ab  = -5 
## node(-2).ab = 2       ## node(-2).ap = 5

class cycle_configuration_graph() :
    def __init__(self, cycles,
                 weight_gray ,
                 weight_black,
                 final_length) :

        # With different content we do not need to check this
        #if (sum(weight_gray) != sum(weight_black)) :
        #    print("Different intergenic regions")
        #    sys.exit()


        ## The number of cycles was never calculated
        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.__first_indice_shift   = 0 # Tell us the index of the
                                        # edge that is pointed by
                                        # begin_node. If it is
                                        # negative, than we know that
                                        # a mirror have occurred.

        ## self.n is the number of black edges. Remember this graph
        ## might not be a permutation
        self.n = 0
        self.final_n = final_length
        for cycle in cycles :
            self.n = self.n + len(cycle)
        n = self.n
          
        # Creating nodes
        node_list = []
        node_list = [cycle_graph_node(i, False) for i in range(2*n)]
        self.begin_node = node_list[0 ]
        self.end_node   = node_list[-1]

        # Creating ap
        for i in range(0,2*n,2) :
            node_list[i  ].ap  = node_list[i+1]
            node_list[i+1].ap  = node_list[i  ]
            weight = weight_black[int(i/2)]
            node_list[i  ].wp  = node_list[i+1].wp  = weight
            
            node_list[i  ].wps  = weight[0]
            node_list[i+1].wps  = weight[0]
            if len(weight) > 1 :
                node_list[i  ].wps  += weight[-1]
                node_list[i+1].wps  += weight[-1]

            node_list[i  ].lp  = len(weight)-1
            node_list[i+1].lp  = len(weight)-1

        # Creating ab
        for i in range(1,2*n-1,2) :
            node_list[i  ].ab  = node_list[i+1]
            node_list[i+1].ab  = node_list[i  ]

        # Creating ac 
        for cycle in cycles :
            for i in range(len(cycle)) :               
                front, back  = -1,-1 # from left of the black edge.
                j = (i+1)%len(cycle)

                if cycle[i] > 0 :
                    front = 2*( cycle[i]  -1 )
                else :
                    front = 2*(-cycle[i]) -1

                if cycle[j] > 0 :
                    back = 2*( cycle[j]) -1
                else :
                    back = 2*(-cycle[j]  -1 )

                #print(front, back)
                node_list[front].ac = node_list[back]
                node_list[back].ac  = node_list[front]

        self.set_values()
        for i in range(0,2*n,1) :
            positive =  min(abs(node_list[i].value),
                            abs(node_list[i].ac.value))
            
            weight = weight_gray[positive]
            node_list[i].wc     = weight
            node_list[i].ac.wc  = weight

            node_list[i].wcs     = weight[0]
            node_list[i].ac.wcs  = weight[0]
            if len(weight) > 1 :
                node_list[i].wcs     += weight[-1]
                node_list[i].ac.wcs  += weight[-1]
            node_list[i].lc     = len(weight)-1
            node_list[i].ac.lc  = len(weight)-1

        insert_iota1 = node_list[0]
        insert_iota2 = insert_iota1.ac
        curr = 1

        insert_iota1.lc_iota = [i for i in range(curr,curr+insert_iota1.lc)]
        insert_iota2.lc_iota = insert_iota1.lc_iota
        
        curr += insert_iota1.lc+1
        insert_iota1 = insert_iota2.ab
        insert_iota2 = insert_iota1.ac
        while True :
            insert_iota1.lc_iota = [i for i in range(curr,curr+insert_iota1.lc)]
            insert_iota2.lc_iota = insert_iota1.lc_iota
            
            curr += insert_iota1.lc+1
            
            insert_iota1 = insert_iota2.ab
            if insert_iota1 == 0 :
                break
            else :
                insert_iota2 = insert_iota1.ac


    ############################################################                
    ################ Rearrangement Operations  #################
    ############################################################ 
    # transposition when model has no indels
    def transposition(self, i, j, k, weight_i, weight_j, weight_k) :
        node_i = None
        node_j = None
        node_k = None

        unp_i, unp_j, unp_k = 0,0,0

        count     = 0
        unp_count = 0

        node = self.begin_node
        # Find the black edges
        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            if count == j :
                node_j = node
                unp_j  = unp_count
            if count == k :
                node_k = node
                unp_k  = unp_count
            node = node.ap.ab
        
        if (weight_i <  0 or weight_i > node_i.wp) :
            print("ERRO: Peso inconsistente no lado esquerdo: i (max = %s: w = %s)" % (
                node_i.wp,
                weight_i
            ) )
            sys.exit()

        if (weight_j < 0 or weight_j > node_j.wp) :
            print("ERRO: Peso inconsistente no meio:  j (max = %s: w = %s)" % (
                node_j.wp,
                weight_j
            ) )
            sys.exit()

        if (weight_k < 0 or weight_k > node_k.wp) :
            print("ERRO: Peso inconsistente no lado direito:  k (max = %s: w = %s)" % (
                node_k.wp,
                weight_k
            ) )
            sys.exit()


        ## Weights that will be exchanged.
        lefti, righti = weight_i, node_i.wp - weight_i
        leftj, rightj = weight_j, node_j.wp - weight_j
        leftk, rightk = weight_k, node_k.wp - weight_k
            
        # Change the edges
        node_i.ap.ap = node_k
        node_j.ap.ap = node_i
        node_k.ap.ap = node_j

        
        aux       = node_i.ap
        node_i.ap = node_j.ap
        node_j.ap = node_k.ap
        node_k.ap = aux

        # Updating weights: Node_i keeps its place, Node_j moved to
        # the third black edge and Node_k is now in the middle.
        node_i.wp = node_i.ap.wp = lefti  + rightj
        node_k.wp = node_k.ap.wp = righti + leftk
        node_j.wp = node_j.ap.wp = rightk + leftj

        #print "novospesos %d %d %d" % (node_i.wp, node_k.wp, node_j.wp)
        
        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.reset_indices()
        return unp_i, unp_j, unp_k
    
    # reversal when model has no indels
    def reversal(self, i, j, weight) :
        node_i = None
        node_j = None

        unp_i, unp_j = 0,0

        count     = 0
        unp_count = 0
        ## These variables are used to return the transposition
        ## applied as integer. ret_i, and ret_j will be the same
        ## as i,j if we do not have ignored black edges
        node = self.begin_node
        # Find the black edges

        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            if count == j+1 :
                node_j = node
                unp_j  = unp_count - 1
            node = node.ap.ab


        if (weight >  0 and weight > node_i.wp) :
            print("ERRO: Peso inconsistente no lado esquerdo: i (max = %s: w = %s)" % (
                node_i.wp,
                weight
            ) )
            sys.exit()

        if (weight < 0 and abs(weight) > node_j.wp) :
            print("ERRO: Peso inconsistente no lado direito:  j (max = %s: w = %s)" % (
                node_j.wp,
                weight
            ) )
            sys.exit()

        nweight_i = node_i.wp - weight
        nweight_j = node_j.wp + weight            
            
        # Change the edges
        node_i.ap.ap = node_j.ap
        node_i.ap.wp = nweight_j        
        node_j.ap.ap = node_i.ap
        node_j.ap.wp = nweight_j        

        node_i.ap  = node_j
        node_i.wp  = nweight_i        
        node_j.ap  = node_i
        node_j.wp  = nweight_i

        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.__num_balanced_cycles  = False                
        self.reset_indices()
        return unp_i, unp_j

    # reversal when model has indels
    def reversal2(self, i, j, x, y, nweight_i, nweight_j) :
        node_i = None
        node_j = None

        unp_i, unp_j = 0,0

        count     = 0
        unp_count = 0
        ## These variables are used to return the reversal
        ## applied as integer. ret_i, and ret_j will be the same
        ## as i,j if we do not have ignored black edges
        node = self.begin_node
        # Find the black edges

        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            if count == j+1 :
                node_j = node
                unp_j  = unp_count - 1
            node = node.ap.ab


        if (x < 0) or (x > sum(node_i.wp)) :
            print("ERRO: Peso inconsistente no lado esquerdo: i (max = %s: w = %s)" % (
                sum(node_i.wp),
                str(x)
            ) )
            sys.exit()

        if (y < 0) or (y > sum(node_j.wp)) :
            print("ERRO: Peso inconsistente no lado direito:  j (max = %s: w = %s)" % (
                sum(node_j.wp),
                str(y)
            ) )
            sys.exit()         



        # Reverse all wp's greater than one between them
        if node_i.index > node_j.index :
            if node_i.index > node_i.ap.index :
                max_reverse_list = node_i.ap.ab
            else :
                max_reverse_list = node_i.ab
            if node_j.index > node_j.ap.index :
                min_reverse_list = node_j.ab
            else :
                min_reverse_list = node_j.ap.ab
        else :
            if node_j.index > node_j.ap.index :
                max_reverse_list = node_j.ap.ab
            else :
                max_reverse_list = node_j.ab
            if node_i.index > node_i.ap.index :
                min_reverse_list = node_i.ab
            else :
                min_reverse_list = node_i.ap.ab

        while min_reverse_list.index <= max_reverse_list.index :
            if len(min_reverse_list.wp) > 1 :
                min_reverse_list.wp = min_reverse_list.wp[::-1]

            min_reverse_list = min_reverse_list.ap
            if len(min_reverse_list.wp) > 1 :
                min_reverse_list.wp = min_reverse_list.wp[::-1]

            min_reverse_list = min_reverse_list.ab


        # Change the black edges
        
        node_i.ap.ap = node_j.ap
        node_i.ap.wp = nweight_j        
        node_j.ap.ap = node_i.ap
        node_j.ap.wp = nweight_j        

        node_i.ap  = node_j
        node_i.wp  = nweight_i        
        node_j.ap  = node_i
        node_j.wp  = nweight_i

        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.__num_balanced_cycles  = False                
        self.reset_indices()
        return unp_i, unp_j

    def indel(self, is_insertion, i, x, elements, intergenic_regions) :
        node_i = None
        unp_i = 0

        count     = 0
        unp_count = 0
        ## These variables are used to return the indel
        ## applied as integer. ret_i will be the same
        ## as i if we do not have ignored black edges

        node = self.begin_node
        # Find the black edges

        while node :
            count = count + 1
            if not node.padded :
                unp_count = unp_count + 1

            if count == i :
                node_i = node
                unp_i  = unp_count
            node = node.ap.ab

        if (x > sum(node_i.wp)) :
            print("ERRO: Posicao da delecao superior ao tamanho total da regiao intergenica: (wp = %s: del = %s: pos_x_size = %s)" % (
                str(node_i.wp),
                str(intergenic_regions),
                str(x)
            ) )
            sys.exit()

        # let us check in which position of wp the indel will affect
        position_x = 0
        curr_pos_x_size = node_i.wp[0]

        while (curr_pos_x_size < x) :
            position_x += 1
            curr_pos_x_size += node_i.wp[position_x]

        if is_insertion :
            if len(elements) == 0 : # just add some size to the intergenic region
                node_i.wp[position_x] += intergenic_regions[0]
                node_i.ap.wp[position_x] = node_i.wp[position_x]
                node_i.wps = node_i.wp[0]
                if len(node_i.wp) > 1 :
                    node_i.wps += node_i.wp[-1]
                node_i.ap.wps = node_i.wps

            else : # add sizes in between and also intergenic regions. this step is applied only
                   # on trivial cycles, otherwise it must be modified to work with non-trivial cycles.
                number_of_new_nodes = 2*len(elements)
                self.n += len(elements)
                new_nodes = [cycle_graph_node(i, False) for i in range(0,number_of_new_nodes)]
                new_nodes_i = new_nodes[0]

                left_weight_orig = x
                right_weight_orig = node_i.wp[0] - x

                left_wc_orig = node_i.wc[0]
                right_wc_orig = node_i.wc[-1]

                # create new black and gray edges of unitary cycles
                j = 1
                for i in range(1,number_of_new_nodes-1,2) :
                    new_nodes[  i].ap = new_nodes[  i].ac = new_nodes[i+1]
                    new_nodes[i+1].ap = new_nodes[i+1].ac = new_nodes[  i]

                    new_nodes[  i].size = new_nodes[i+1].size = 1

                    new_nodes[  i].blacks = new_nodes[  i].wps = intergenic_regions[j]
                    new_nodes[i+1].blacks =  new_nodes[i+1].wps = intergenic_regions[j]
                    new_nodes[  i].wp = new_nodes[i+1].wp = [intergenic_regions[j],]

                    new_nodes[  i].grays = new_nodes[  i].wcs = node_i.wc[j]
                    new_nodes[i+1].grays = new_nodes[i+1].wcs = node_i.wc[j]
                    new_nodes[  i].wc = new_nodes[i+1].wc = [node_i.wc[j],]

                    new_nodes[  i].lc = len(new_nodes[  i].wc)-1
                    new_nodes[  i].lp = len(new_nodes[  i].wp)-1
                    new_nodes[i+1].lc = len(new_nodes[i+1].wc)-1
                    new_nodes[i+1].lp = len(new_nodes[i+1].wp)-1

                # create white edges between new edges
                for i in range(0,number_of_new_nodes-1,2) :
                    new_nodes[  i].ab = new_nodes[i+1]
                    new_nodes[i+1].ab = new_nodes[  i]

                # link new edges in the extremities with the old ones
                new_nodes[ 0].ap = new_nodes[ 0].ac = node_i
                new_nodes[-1].ap = new_nodes[-1].ac = node_i.ac
                node_i.ac.ap = node_i.ac.ac = new_nodes[-1]
                node_i.ac = node_i.ap = new_nodes[0]

                new_nodes[ 0].blacks    = new_nodes[ 0].wps    = left_weight_orig + intergenic_regions[0]
                new_nodes[ 0].ap.blacks = new_nodes[ 0].ap.wps = left_weight_orig + intergenic_regions[0]
                new_nodes[ 0].wp = new_nodes[ 0].ap.wp = [int(left_weight_orig + intergenic_regions[0]),]

                new_nodes[ 0].grays    = new_nodes[ 0].wcs    = left_wc_orig
                new_nodes[ 0].ac.grays = new_nodes[ 0].ac.wcs = left_wc_orig
                new_nodes[ 0].wc = new_nodes[ 0].ac.wc = [left_wc_orig,]

                new_nodes[-1].blacks    = new_nodes[-1].wps    = right_weight_orig + intergenic_regions[-1]
                new_nodes[-1].ap.blacks = new_nodes[-1].ap.wps = right_weight_orig + intergenic_regions[-1]
                new_nodes[-1].wp = new_nodes[-1].ap.wp = [int(right_weight_orig + intergenic_regions[-1]),]

                new_nodes[-1].grays    = new_nodes[-1].wcs    = right_wc_orig
                new_nodes[-1].ac.grays = new_nodes[-1].ac.wcs = right_wc_orig
                new_nodes[-1].wc = new_nodes[-1].ac.wc = [right_wc_orig,]

                new_nodes[ 0].lc    = len(new_nodes[ 0].wc)-1
                new_nodes[ 0].lp    = len(new_nodes[ 0].wp)-1
                new_nodes[ 0].ac.lc = len(new_nodes[ 0].ac.wc)-1
                new_nodes[ 0].ap.lp = len(new_nodes[ 0].ap.wp)-1
                new_nodes[-1].lc    = len(new_nodes[-1].wc)-1
                new_nodes[-1].lp    = len(new_nodes[-1].wp)-1
                new_nodes[-1].ac.lc = len(new_nodes[-1].ac.wc)-1
                new_nodes[-1].ap.lp = len(new_nodes[-1].ap.wp)-1

                self.set_values()


        else : #we have a deletion
            tam_ir_removed = len(intergenic_regions)
            tam_ir_now = len(node_i.wp) - position_x

            if (tam_ir_removed > tam_ir_now) :
                print("ERRO: Delecao de mais blocos de regioes intergenicas que a regiao possui: (wp = %s: del = %s: start_pos_index = %s)" % (
                    str(node_i.wp),
                    str(intergenic_regions),
                    str(position_x)
                ) )
                sys.exit()

            if (intergenic_regions[1+position_x:-1] != node_i.wp[1+position_x:tam_ir_removed-1]) :
                print("ERRO: Delecao de regioes intermediarias nao consistentes com o existente: (wp = %s: del = %s: start_pos_index = %s)" % (
                    str(node_i.wp),
                    str(intergenic_regions),
                    str(position_x)
                ) )
                sys.exit()

            if tam_ir_removed > 1 :
                node_i.wp = node_i.wp[:position_x] + [ int(node_i.wp[position_x] - intergenic_regions[0] + node_i.wp[position_x + tam_ir_removed - 1] - intergenic_regions[-1]),] + node_i.wp[position_x + tam_ir_removed:]
                node_i.ap.wp = node_i.wp[:]
                node_i.wps = node_i.wp[0]
                if len(node_i.wp) > 1 :
                    node_i.wps += node_i.wp[-1]
                node_i.ap.wps = node_i.wps
                node_i.lp = len(node_i.wp)-1
                node_i.ap.lp = len(node_i.ap.wp)-1
            else :
                node_i.wp = node_i.wp[:position_x] + [int(node_i.wp[position_x] - intergenic_regions[position_x]),] + node_i.wp[position_x + tam_ir_removed:]
                node_i.ap.wp = node_i.wp[:]

            if (node_i.wp[position_x] < 0) :
                print("ERRO: A região intergenica resultante na posicao afetada ficou com peso negativo: (wp = %s: del = %s: start_pos_index = %s)" % (
                    str(node_i.wp),
                    str(intergenic_regions),
                    str(position_x)
                ) )
                sys.exit()

        self.__num_cycles           = False
        self.__num_odd_cycles       = False
        self.__num_balanced_cycles  = False                
        self.reset_indices()
        return unp_i

    ############################################################                
    ################### Auxiliary Methods  #####################
    ############################################################                
    def print_indices(self) :
        node = self.begin_node

        while node :
            print("%i, padded = %s" % (node.index, node.padded))
            node = node.ap
            print("%i, padded = %s" % (node.index, node.padded))
            node = node.ab

    def to_string(self) :
        self.clean_visit()        

        node = self.end_node        

        str_cycles = "("

        while node :
            if not node.visit :
                cycle_node = node
                cycle      = "("

                while not cycle_node.visit :
                    wc = cycle_node.wc
                    wp = cycle_node.wp
                    lc = cycle_node.lc
                    lp = cycle_node.lp
                    if cycle_node.index % 2 == 0 :
                        cycle = cycle + "%i<%s,%s>," % (-(cycle_node.index+2)/2,str(wp),str(wc))
                    else :
                        cycle = cycle + "%i<%s,%s>," % (+(cycle_node.index+1)/2,str(wp),str(wc))


                    cycle_node.visit = True
                    cycle_node = cycle_node.ap
                    cycle_node.visit  = True
                    cycle_node = cycle_node.ac
                    
                cycle = cycle[:-1] + "),"
                str_cycles = str_cycles + cycle
            node = node.ap.ab
        str_cycles = str_cycles[:-1] + ")"
        return str_cycles

            

    def get_cycles(self, want_vertices = False) :
        self.clean_visit()        

        node = self.end_node        
        cycles    = []
        vertices  = []

        while node :
            if not node.visit :
                cycle_node  = node
                cycle       = []
                cycle_nodes = []

                while not cycle_node.visit :
                    if cycle_node.index % 2 == 0 :
                        cycle.append( -(cycle_node.index+2)/2 )
                    else :
                        cycle.append( +(cycle_node.index+1)/2 )


                    cycle_node.visit = True
                    cycle_nodes.append(cycle_node)
                    cycle_node = cycle_node.ap
                    cycle_node.visit  = True
                    cycle_nodes.append(cycle_node)
                    cycle_node = cycle_node.ac
                    
                cycles.append(tuple(cycle))
                vertices.append(cycle_nodes)

            node = node.ap.ab
        if want_vertices :
            return tuple(cycles), vertices
        return tuple(cycles)


    def permutation(self) :
        self.set_values()
        permutation = ""
        node = self.begin_node 
        while node :
            if type(node.value) == bool :
                return ""
            node = node.ap
            if type(node.value) == bool :
                return ""
            node = node.ab

            if not type(node) == int :
                permutation += "%i," % node.value
        return permutation[:-1]

    ## Here we try to give values to the nodes to check if they are a
    ## permutation.
    def set_values(self) :
        node = self.begin_node        

        node.value = 0
        node = node.ac
        node.value = -1

        while node.ab :
            node = node.ab
            node.value = -(node.ab.value)
            node = node.ac

            if node.ac.value > 0 :
                node.value = -(node.ac.value + 1)
            else :
                node.value = -(node.ac.value - 1)
    
    def reset_indices(self) :
        node  = self.begin_node 
        count = 0

        while node :
            node.index = count

            node.lp    = len(node.wp)-1
            node.lc    = len(node.wc)-1

            node       = node.ap
            count      = count + 1
            
            node.index = count

            node.lp    = len(node.wp)-1
            node.lc    = len(node.wc)-1

            node       = node.ab
            count      = count + 1

    def num_cycles(self) :
        if type(self.__num_cycles) == bool :
            self.calculate_cycles()
        return self.__num_cycles

    def num_odd_cycles(self) :
        if type(self.__num_odd_cycles) == bool :
            self.calculate_cycles()
        return self.__num_odd_cycles


    def calculate_cycles(self) :
        cycles, vertices = self.get_cycles(want_vertices = True)
        num_cycles = len(cycles)
        num_odd = 0
        is_labeled = False

        for cycle in cycles :
            if len(cycle) % 2 == 1 :
                num_odd = num_odd + 1

        self.__num_cycles           = num_cycles
        self.__num_odd_cycles       = num_odd

        for i in range(len(cycles)) :            
            cycle = cycles[i]
            size = len(cycle)

            direction = 1
            for el in cycle :
                if (el < 0) :
                    direction = 2
                    break

            blacks   = 0
            grays    = 0
            vertice_set = vertices[i]
            is_gray_labeled = False
            is_black_labeled = False
            for vertex in vertice_set :
                if (vertex.lc == 0) :
                    grays   = grays   + vertex.wc[0]
                else :
                    is_gray_labeled = True
                    grays   = grays   + vertex.wc[0] + vertex.wc[-1]
                if (vertex.lp == 0):
                    blacks  = blacks  + vertex.wp[0]
                else :
                    is_black_labeled = True
                    blacks  = blacks  + vertex.wp[0] + vertex.wp[-1]
            grays  = grays  / 2
            blacks = blacks / 2

            vertice_set = vertices[i]
            for vertex in vertice_set :
                vertex.size      = size
                vertex.grays     = grays
                vertex.blacks    = blacks
                vertex.direction = direction                
                #vertex.kind  = kind
                vertex.cycle = i
                vertex.gray_labeled = is_gray_labeled
                vertex.black_labeled = is_black_labeled

    def clean_visit(self) :
        node = self.begin_node
        
        while node :
            node.visit = False
            node       = node.ap
            node.visit = False
            node       = node.ab



############################################################################
############### Do not need to sort a real permutation #####################
############################################################################

## This class was developed to sort cycle-graph configurations. We
## apply several rules in order to make the configuration closer to
## the identity. If no rule is found, so the program returns with no
## error message. 

## If the input cycle configuration is a full component, then we
## guarantee that the final permutation is the identity.

class Intergenic_Rev :
    def __init__(self, cycles, wgray, wblack, final_length) :
        self.input_cycles  = str(cycles).replace(" ", "")
        self.input_wgray   = str(wgray).replace(" ", "")[1:-1]
        self.input_wblack  = str(wblack).replace(" ", "")[1:-1]
                        
        self.graph      = cycle_configuration_graph(cycles,
                                                    wgray,
                                                    wblack,
                                                    final_length)
        self.randomized = False

    def get_num_balanced(self, vertices) :
        num_balanced = 0
        for vertice in vertices :
            if vertice[0].grays == vertice[0].blacks :
                num_balanced = num_balanced + 1
        return num_balanced

    def get_num_clean_balanced(self, vertices) :
        num_balanced = 0
        for vertice in vertices :
            if vertice[0].grays == vertice[0].blacks and vertice[0].black_labeled == False and vertice[0].gray_labeled == False:
                num_balanced = num_balanced + 1
        return num_balanced
    
    def sort(self, start_time, is_3approx) :
        sequence = []
        graph = self.graph

        graph.calculate_cycles()
        _, vertices = graph.get_cycles(want_vertices = True)
        num_balanced = self.get_num_clean_balanced(vertices)
        if DEBUG :
            print("NUM BALANCED --> %s" % num_balanced)

        lbc = graph.n - num_balanced
        ##lowertransp
        #lowerb = (1.0*lbc)/2.0
        ##lowerrev
        lowerb = 1.0*lbc
        while True :
            #print graph.get_cycles()
            #print graph.to_string()
            #graph.calculate_cycles()
            ####print("GRAFO ATUAL",graph.to_string())
            #permaux = eval("[%s]" % graph.permutation())
            #permauxneg = sum(1 for nneg in permaux if nneg < 0)
            ####print("NNNNNNNEG ATUAL", permauxneg)

            #_, vertices = graph.get_cycles(want_vertices = True)
            #num_balanced = 0
            #for vertice in vertices :
            #    print "black = %d gray = %d" % (vertice[0].blacks, vertice[0].grays)
            #    if vertice[0].grays == vertice[0].blacks :
            #        num_balanced = num_balanced + 1
            operations  =  self.search_rev_indel(graph, is_3approx)
            #print(sequence)
            #print(graph.to_string())
            if not operations :
                break

            if DEBUG :
                print("##############################")
                print(graph.to_string())            
            for op in operations :
                if callable(op[0]) :
                    graph.calculate_cycles()
                    if DEBUG :
                        print("calling : ", op[1].index, op[2].index, op[3].index)
                    append = op[0](*tuple(op[1:]))
                    for el in append :
                        operations.append(el)
                else :
                    #print(op)
                    op = self.format_node_to_operations_indel(op)
                    if DEBUG :
                        print("OPERACAO", op)
                    if op[0] == 0 :
                        graph.indel(op[0], op[1],op[2],op[3][0], op[3][1])
                        sequence.append(tuple(['DEL', op[1], op[2], op[3][0], op[3][1]]))
                    if op[0] == 1 :
                        graph.indel(op[0], op[1],op[2],op[3][0], op[3][1])
                        sequence.append(tuple(['INS', op[1], op[2], op[3][0], op[3][1]]))
                    if op[0] == 2 :
                        graph.reversal2(op[1],op[2],op[3][0], op[3][1], op[3][2], op[3][3])
                        sequence.append(tuple(['REV',op[1],op[2],op[3][0],op[3][1]]))
                    if DEBUG :
                        print(graph.to_string())
                    #print(op)
                    #print(graph.to_string())
                        
            ##################################################                    
            # Abaixo apenas depuracao        
            ##################################################
            graph.calculate_cycles()
            _, vertices = graph.get_cycles(want_vertices = True)
            num_balanced = self.get_num_balanced(vertices)
            #print(graph.to_string())
            if DEBUG :
                print("NUM BALANCED -->%s \n" % num_balanced)
            #sys.exit()
            
            
        graph.calculate_cycles()
        _, vertices = graph.get_cycles(want_vertices = True)
        num_balanced = 0
        for vertice in vertices :
            if vertice[0].grays == vertice[0].blacks :
                num_balanced = num_balanced + 1

        if num_balanced == graph.final_n :
            if (((1.0*len(sequence))/lowerb) <= 3) :
                print('%s [%s] [%s] %d %s %f %f' % (self.input_cycles,
                               self.input_wgray,
                               self.input_wblack,
                               len(sequence),
                               str(sequence).replace(" ", ""),
                               len(sequence)/lowerb,
                               float(time.time() - start_time)))
            else :
                print('%s [%s] [%s] %d %s %f %f ERROR-LOWER-BOUND-HIGHER' % (self.input_cycles,
                               self.input_wgray,
                               self.input_wblack,
                               len(sequence),
                               str(sequence).replace(" ", ""),
                               len(sequence)/lowerb,
                               time.time() - start_time))
        else :
            print('%s [%s] [%s] %d %s %f %f ERROR-NOT-SORTED' % (self.input_cycles,
                               self.input_wgray,
                               self.input_wblack,
                               len(sequence),
                               str(sequence).replace(" ", ""),
                               len(sequence)/lowerb,
                               time.time() - start_time))
     

    def format_node_to_operations_indel(self,operation) :
        if operation :
            if operation[0] == 2 : #rev
                #i = int(round(float(operation[1].index + 1) / 2))
                #j = int(round(float(operation[2].index + 1) / 2))
                i = int(math.ceil(float(operation[1].index + 1) / 2))
                j = int(math.ceil(float(operation[2].index + 1) / 2))
                return(2, i, j-1, operation[3])
            else : #indel
                #i = int(round(float(operation[1].index + 1) / 2))
                i = int(math.ceil(float(operation[1].index + 1) / 2))
                return(operation[0], i, operation[2], operation[3])


    ## Para reversões com indels
    def search_rev_indel(self, graph, is_3approx = True) :
        graph.calculate_cycles()
        operations = None
        
        if not operations :
            ## We will transform a trivial cycle C that is not black-labeled
            ## and it is either clean and unbalanced or gray-labeled and
            ## positive into a clean and balanced cycle
            operations = self.lemma_5(graph)
            if operations :
                return [operations]

        if not operations :
            ## We will transform a trivial cycle C that does not fit into
            ## lemma 5 (i.e., it is black-labeled or it is gray-labeled 
            ## and negative) into a clean and balanced cycle
            operations = self.lemma_6(graph)
            if operations :
                return [operations]

        if not operations :
            ## We will break a non-trivial cycle C that is divergent
            ## and not clean.
            operations = self.lemma_7(graph)
            if operations :
                return [operations]

        if not operations :
            ## We will break a non-trivial cycle C that is divergent
            ## and clean.
            operations = self.lemma_8(graph)
            if operations :
                return [operations]

        if not operations and is_3approx :
            ## At this step no divergent cycle exists. We will apply 
            ## a reversal that creates a new divergent cycle.
            operations = self.lemma_9(graph)
            if operations :
                return [operations]
        if not operations and not(is_3approx) :
            ## At this step no divergent cycle exists. We will apply 
            ## a reversal to an oriented cycle that creates a new 
            ## divergent cycle.
            operations = self.lemma_10(graph)
            if operations :
                return [operations]
        if not operations and not(is_3approx) :
            ## At this step no divergent cycle exists. We will apply 
            ## a reversal to any non trivial cycle that creates a new 
            ## divergent cycle.
            operations = self.lemma_11(graph)
            if operations :
                return [operations] 

##################################################
############### Several Steps ####################
##################################################


    ## Receive two nodes in the same cycle.
    def __check_convergency(self, graph, v_i, v_j) :
        if v_i.cycle == v_j.cycle :
            
            node = v_i.ap.ac 
            while node.index != v_i.index :
                node = node.ap.ac 
                if node.index == v_j.index :                    
                    return True
            return False
        print ("Error: Edges in different cycles")
        sys.exit()


    ## Search crossing edges. The point of this method is to find a
    ## reversal that transforms two black edges that are convergent
    ## into two black edges that are divergent. I will usually put
    ## these two black edges as parameters.
    def __search_crossing_edges(self, graph, v_i, v_j, any_cycle = False) :
        ## b is the rightmost and in the right side of the black edge
        a,b = v_i, v_j
        if a.index > b.index :
            a,b = b,a
        if a.index % 2 == 0 :
            a = a.ap
        if b.index % 2 == 0 :
            b = b.ap

        half1 = {}
        half2 = {}
        
        ## starting the search
        node = graph.end_node
        while node != b :
            half1[node.cycle] = node
            node = node.ap.ab
                    
        node = b.ap.ab
        while node != a :
            half2[node.cycle] = node
            node = node.ap.ab
        
        node = a.ap.ab
        while node :
            half1[node.cycle] = node
            node = node.ap.ab

        for key in list(half1.keys()) :
            if key in half2 :
                a,b = half1[key], half2[key]
                if ( key != v_i.cycle or
                     self.__check_convergency(graph, a, b) ) :
                    if a.index > b.index :
                        a,b = b,a
                    return a,b

    ## This is an auxiliary method called in the next method for
    ## simplicity. Remember we are talking about reversals. In order
    ## to understand this method, we advise you to draw the four cases
    ## in a piece of paper and try to code.
    def __indel_compute_balance(self, v_i, v_j, balance, available, go_right):
        ## Check if the first cycle can be
        ## balanced. Keep in mind that balance
        ## refers to the cycle that will have v_i.
        if (0 <= balance <= available) :
            a, b = v_j, v_i
            if (v_i.index < v_j.index) :
                a,b = v_i, v_j
            exchange = balance - a.wp[0]
            
            if go_right : ## We need balance in
                          ## the right                                    
                return (a,b, balance - b.wp[0]) 
            else : ## We need balance in the left
                return (a, b, a.wp[0] - balance) 

    ## This should be applied on black edges v_i and v_j in the same
    ## cycle. The inputs partial_gray and partial_black represents the
    ## gray and black edges that goes from v_i to v_j starting from a
    ## gray edge. In this case, it is going to be the gray edges in a
    ## cycle that would be formed if the reversal was applied
    def __indel_get_balance(self, v_i, v_j, partial_gray, partial_black) :
                        
        ## E necessario desenhar os casos no papel para entender a
        ## linha abaixo.
        v_i_right     = (v_i.index > v_i.ap.index)
        balance      = partial_gray - partial_black

        grays  = v_i.grays  ## Sum of gray  edges
        blacks = v_i.blacks ## Sum of black edges

        available=v_i.wp[0] + v_j.wp[0] ## Amount of
                                  ## weight that
                                  ## can go to any
                                  ## cycle.
        #print("aa",v_i.index, v_j.index, available, balance,
        #      partial_gray, partial_black)


        go_right = v_i_right
        op = self.__indel_compute_balance(v_i, v_j, balance, available, go_right)
        if op :
            return op
        
        go_right     = not  v_i_right                            
        remain_gray  = grays  - partial_gray 
        remain_black = blacks - partial_black - available
        balance     = remain_gray - remain_black
        op = self.__indel_compute_balance(v_i, v_j, balance, available, go_right)
        if op :
            return op


    def find_all_triples(self, cycle) :
        triples = []
        k = cycle[0]

        while True :  ## Loop over k
            i = k.ap.ac
            while True : ## Loop over i
                j = i.ap.ac                
                while True : ## Loop over j
                    if (k.index > j.index > i.index) :
                        triples.append([i, j, k] )
                    j = j.ap.ac
                    if j.index == k.index :
                        break
                i = i.ap.ac
                if i.ap.ac.index == k.index :
                    break            
            k = k.ap.ac
            if k.index == cycle[0].index :
                break
            
        #for triple in triples :
        #    print("Triples: ", triple[0].index, triple[1].index, triple[2].index)        
        return(triples)

    ## First lemma, we will try to transform a trivial not black-labeled cycle
    ## that is (i) not balanced or (ii) gray-labeled and non-negative into a 
    ## balanced clean cycle using one indel
    def lemma_5(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if cycle[0].size == 1 and cycle[0].lp == 0 and (
                 (cycle[0].lc == 0 and cycle[0].blacks != cycle[0].grays) or 
                 (cycle[0].lc > 0 and cycle[0].blacks <= cycle[0].grays)
            ) :
                if cycle[0].lc == 0 : ## we just modify the weight of the black edge
                    indel_position = 0
                    indel_sequence = [int(cycle[0].wc[0] - cycle[0].wp[0]),]
                    operation = 1
                    pi_inserted = []
                    if indel_sequence[0] < 0 :
                        operation = 0
                        indel_sequence[0] = -indel_sequence[0]
                else : ## we must add some new elements
                    operation = 1
                    pi_inserted = cycle[0].lc_iota
                    if ((cycle[0].index > cycle[0].ap.index and cycle[0].value > 0) or
                       (cycle[0].index < cycle[0].ap.index and cycle[0].value < 0)) :
                        pi_inserted = [-i for i in pi_inserted[::-1]]
                        cycle[0].wc = cycle[0].ap.wc = cycle[0].wc[::-1]
                    if (cycle[0].wc[0] >= cycle[0].wp[0]) :
                        indel_position = cycle[0].wp[0]
                        indel_sequence = [int(cycle[0].wc[0] - cycle[0].wp[0]),] + cycle[0].wc[1:]
                    else :
                        indel_position = cycle[0].wc[0]
                        indel_sequence = [0, ] + cycle[0].wc[1:]
                        indel_sequence[-1] = max(0,int(indel_sequence[-1] - (cycle[0].wp[0] - cycle[0].wc[0])))
                return (operation, cycle[0], indel_position, [pi_inserted, indel_sequence])
        return None

    ## Second lemma, we will try to transform a trivial black-labeled cycle
    ## into a trivial not black-labeled cycle, and eventually apply lemma_5
    def lemma_6(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].size == 1) and (cycle[0].lp > 0 or cycle[0].blacks > cycle[0].grays) :
                if (cycle[0].lp > 0) : #we will remove some alphas
                    if (cycle[0].wp[0] >= cycle[0].grays) :
                        indel_position = cycle[0].grays
                        indel_sequence = [int(cycle[0].wp[0] - cycle[0].grays),] + cycle[0].wp[1:]
                    elif (cycle[0].wp[-1] >= cycle[0].grays) :
                        indel_position = 0
                        indel_sequence = cycle[0].wp[:-1] + [int(cycle[0].wp[-1] - cycle[0].grays),]
                    elif (cycle[0].wp[0] + cycle[0].wp[-1] >= cycle[0].grays) :
                        indel_position = cycle[0].wp[0]
                        indel_sequence = [0,] + cycle[0].wp[1:-1] + [int(cycle[0].wp[-1]+cycle[0].wp[0]-cycle[0].grays),]
                    else : #lemma_5 will be applied after this...
                        indel_position = cycle[0].wp[0]
                        indel_sequence = [0,] + cycle[0].wp[1:-1] + [0,]
                else : # we will just remove an intergenic size
                    indel_position = 0
                    indel_sequence = [cycle[0].blacks - cycle[0].grays]
                return (0, cycle[0], indel_position, [[0 for _ in range(0,cycle[0].lp)], indel_sequence])
        return None

    ## Third lemma, we will try to transform a divergent cycle C into one trivial
    ## not black-labeled cycle and one cycle with the remaining edges
    ## after this lemma, we may apply lemma 5 in the trivial one.
    def lemma_7(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].direction == 2) and (cycle[0].gray_labeled == True or cycle[0].black_labeled == True) :
                start_point = cycle[0]
                a = cycle[0]
                b = a.ap.ac
                trivial, other = None, None
                if (a.index%2 != b.index%2) :
                    if a.index > a.ap.index :
                        if a.index < b.index :
                            trivial, other = a, b
                        else :
                            trivial, other = b, a
                    else :
                        if a.index < b.index :
                            trivial, other = b, a
                        else :
                            trivial, other = a, b
                    
                else :
                    a = a.ap.ac
                    b = b.ap.ac
                    while (a.index != start_point.index) and (trivial == None) :
                        if (a.index%2 != b.index%2) :
                            if a.index > a.ap.index :
                                if a.index < b.index :
                                    trivial, other = a, b
                                else :
                                    trivial, other = b, a
                            else :
                                if a.index < b.index :
                                    trivial, other = b, a
                                else :
                                    trivial, other = a, b
                        else :
                            a = a.ap.ac
                            b = b.ap.ac

                if trivial != None :
                    length_needed = trivial.wc[0]
                    if len(trivial.wc) > 1 :
                        length_needed += trivial.wc[-1]

                    if trivial.index < other.index : ## a trivial cycle will be created in the left
                        if (trivial.wp[0] + other.wp[0] >= length_needed) :
                            cut_left_ir = min(length_needed, trivial.wp[0])
                            cut_right_ir = length_needed - cut_left_ir
                            res_left_ir = [length_needed,]
                            res_right_ir = trivial.wp[1:][::-1] + [int(other.wp[0] + trivial.wp[0] - length_needed),] + other.wp[1:]
                        else :
                            cut_left_ir = trivial.wp[0]
                            cut_right_ir = other.wp[0]
                            res_left_ir = [int(trivial.wp[0] + other.wp[0]),]
                            res_right_ir = trivial.wp[1:][::-1] + [0,] + other.wp[1:]
                        return(2,trivial,other,[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
                    else : ## a trivial cycle will be created in the right)
                        if (trivial.wp[-1] + other.wp[-1] >= length_needed) :
                            already_in_the_right = min(length_needed, trivial.wp[-1])
                            cut_right_ir = sum(trivial.wp[:-1]) + trivial.wp[-1] - already_in_the_right
                            cut_left_ir =  sum(other.wp[:-1]) + (other.wp[-1] + trivial.wp[-1] - already_in_the_right)
                            res_left_ir = other.wp[:-1] + [int(trivial.wp[-1] + other.wp[-1] - length_needed),] + trivial.wp[:-1][::-1] 
                            res_right_ir = [length_needed,]
                        else :
                            cut_left_ir = sum(other.wp[:-1])
                            cut_right_ir = sum(trivial.wp[:-1])
                            res_left_ir =  other.wp[:-1] + [0,] + trivial.wp[:-1][::-1]
                            res_right_ir = [int(other.wp[-1]+trivial.wp[-1]),]
                        return(2,trivial,other,[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
        return None

    ## Fourth lemma, we will try to transform a divergent clean cycle C:
    ##  (  i) into a balanced cycle, if C is positive
    ##  ( ii) into two balanced cycles, if C is balanced
    ##  (iii) into one balanced cycle and one negative cycle otherwise
    def lemma_8(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
            if (cycle[0].direction == 2) and (cycle[0].gray_labeled == False) and (cycle[0].black_labeled == False) :

                if (cycle[0].grays > cycle[0].blacks) : ## C is a positive cycle
                    indel_sequence = [int(cycle[0].grays - cycle[0].blacks),]
                    return(1,cycle[0], 0, [[], indel_sequence])
                else :  
                    for i in range(1, len(cycle) - 2, 2) :
                        v_i           = cycle[i]
                        
                        partial_gray  =  v_i.wc[0]
                        partial_black =  0
                        for j in range(i+2, len(cycle), 2)  :
                            v_j           = cycle[j]

                            if (v_i.index%2 != v_j.index%2): ## Check divergence
                                op = self.__indel_get_balance(v_i, v_j, partial_gray, partial_black)
                                if op :
                                    if op[2] >= 0 :
                                        cut_left_ir = op[0].wp[0] - op[2]
                                        cut_right_ir = 0
                                        res_left_ir = [cut_left_ir,]
                                        res_right_ir = [int(op[1].wp[0] + op[2]),]
                                    else :
                                        cut_left_ir = op[0].wp[0]
                                        cut_right_ir = -op[2]
                                        res_left_ir = [int(cut_left_ir - op[2]),]
                                        res_right_ir = [int(op[1].wp[0] + op[2]),]
                                    return(2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
                                
                            ## Preparing next iteration    
                            partial_gray  = partial_gray  + v_j.wc[0]
                            partial_black = partial_black + v_j.wp[0]
        return None

    # Lemma 9 of the preliminary version (paper presented at AlCoB 2021: Reversal Distance on Genomes with Different Gene Content and Intergenic Regions Information) 
    # This Lemma was replaced by two other lemmas in the final manuscript published at IEEE/ACM Transactions on Computational Biology and Bioinformatics
    def lemma_9(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
          if cycle[0].size > 1 :#and cycle[0].grays <= cycle[0].blacks :
            #print(str(cycle[0]),cycle[0].grays, cycle[0].blacks)
            for i in range(1, len(cycle) - 2, 2) :
                v_i           = cycle[i]
                partial_gray  =  v_i.wc[0]
                partial_black =  0
                for j in range(i+2, len(cycle), 2)  :
                    v_j           = cycle[j]
                    #op = self.__indel_get_balance(v_i, v_j, partial_gray, partial_black)
                    #if op :
                    op = self.__search_crossing_edges(graph, v_i, v_j)
                    if op :
                        cut_left_ir = sum(op[0].wp)
                        cut_right_ir = 0
                        res_left_ir = op[0].wp
                        res_right_ir = op[1].wp
                        return(2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
                            
                    ## Preparing next iteration    
                    partial_gray  = partial_gray  + v_j.wc[0]
                    partial_black = partial_black + v_j.wp[0]
        ##if there is no crossing cycles, all long cycles are oriented.
        for cycle in vertices :
          if cycle[0].size > 2 :#and cycle[0].grays <= cycle[0].blacks :
            triples = self.find_all_triples(cycle)
            if triples :
                op = [triples[0][1], triples[0][2]]
                cut_left_ir = sum(op[0].wp)
                cut_right_ir = 0
                res_left_ir = op[0].wp
                res_right_ir = op[1].wp
                return(2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])

        return None

    ## This lemma searches for an oriented convergent cycle, and will transform
    ## it into a divergent cycle
    ## This was changed to Lemma 9 in the final version of the paper
    def lemma_10(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
          if cycle[0].size > 2 :#and cycle[0].grays <= cycle[0].blacks :
            triples = self.find_all_triples(cycle)
            if triples :
                op = [triples[0][1], triples[0][2]]
                cut_left_ir = sum(op[0].wp)
                cut_right_ir = 0
                res_left_ir = op[0].wp
                res_right_ir = op[1].wp
                return(2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])

        return None        

    ## last step: there are only non-oriented convergent cycles
    ## This was changed to Lemma 10 in  the final version of the paper
    def lemma_11(self, graph) :
        _, vertices = graph.get_cycles(want_vertices = True)
        for cycle in vertices :
          if cycle[0].size > 1 :#and cycle[0].grays <= cycle[0].blacks :
            #print(str(cycle[0]),cycle[0].grays, cycle[0].blacks)
            for i in range(1, len(cycle) - 2, 2) :
                v_i           = cycle[i]
                partial_gray  =  v_i.wc[0]
                partial_black =  0
                for j in range(i+2, len(cycle), 2)  :
                    v_j           = cycle[j]
                    #op = self.__indel_get_balance(v_i, v_j, partial_gray, partial_black)
                    #if op :
                    op = self.__search_crossing_edges(graph, v_i, v_j)
                    if op :
                        cut_left_ir = sum(op[0].wp)
                        cut_right_ir = 0
                        res_left_ir = op[0].wp
                        res_right_ir = op[1].wp
                        return(2,op[0],op[1],[cut_left_ir, cut_right_ir, res_left_ir, res_right_ir])
                            
                    ## Preparing next iteration    
                    partial_gray  = partial_gray  + v_j.wc[0]
                    partial_black = partial_black + v_j.wp[0]

        return None

########################################################################## 
## Auxiliary functions to transform the input into the instance we want
##########################################################################       

def get_position(permutation) :
    n = len(permutation)-2
    position    = [-1 for i in range(0, n+2)]
    for i in range(0, n+2) :
        position[abs(permutation[i])] = i
    return position

def get_rightmost_element(cycle, position) :
    max_position = 0
    for i in range(len(cycle)) :
        if position[cycle[i]] > position[cycle[max_position]] :
            max_position = i
    return max_position

## The unordered cycle starts with a gray edge, we order them by
## making it start with the rightmost black edge.
def order_cycle(cycle, position) :
    index = get_rightmost_element(cycle, position)
    new   = []
    new.append(cycle[index])

    if index % 2 == 0 :
        iter_el  = (index-1) % len(cycle)
        while iter_el != index :
            new.append(cycle[iter_el])
            iter_el = (iter_el-1) % len(cycle)
    else :
        iter_el  = (index+1) % len(cycle)
        while iter_el != index :
            new.append(cycle[iter_el])
            iter_el = (iter_el+1) % len(cycle)
    return new

def canonical_representation(cycle, position) :
    cycle     = order_cycle(cycle, position)
    canonical = []

    for i in range(0,len(cycle),2) :
        if position[cycle[i]] < position[cycle[i+1]] :
            black = -position[cycle[i+1]]
            canonical.append(black )
        else :
            black = position[cycle[i]]
            canonical.append(black)
    return canonical

def construct_black_edges(input_string, input_black) :
    wblack = []
    input_string_numbers = []
    interblack = []
    for i in range(0,len(input_string)) :
        num = input_string[i]
        interblack.append(input_black[i])
        if num != 0 :
            input_string_numbers.append(num)
            wblack.append(interblack)
            interblack = []

    i = len(input_string)
    while i < len(input_black) :
        interblack.append(input_black[i])
        i += 1
    if len(interblack) > 0 :
        wblack.append(interblack)
    return(wblack, input_string_numbers)

def construct_str_cycle(input_string, input_gray, input_black) :

    # Given the input_black weights, let us group them according
    # to the edges in the cycle graph (i.e., we just group the
    # values on positions where input_string is 0)
    wblack, input_string_numbers = construct_black_edges(input_string, input_black)

    # Get the maximum number in input_string and add the paddings (i.e., 0 and n+1)
    max_input_string_numbers = max(max(input_string_numbers),-1*min(input_string_numbers))
    input_string_numbers = [0] + input_string_numbers + [max_input_string_numbers+1]

    # This is a vector that says if an element is present or not in the input_string
    element_exists = [-1 for i in range(0,max_input_string_numbers+2)]
    for element in input_string_numbers :
        element_exists[abs(element)] = 0

    # Sort the elements in the input_string to help with the gray edges generation
    sorted_input_string = [abs(el) for el in input_string_numbers]
    sorted_input_string.sort()

    # Here we genarate the gray edges weights using the input_gray
    wgray = []
    for i in range(1,len(sorted_input_string)-1) :
        intergray = input_gray[sorted_input_string[i-1]:sorted_input_string[i]]
        wgray.append(intergray)
    intergray = input_gray[sorted_input_string[i]:]
    wgray.append(intergray)

    # Now we generate a corresponding permutation using the input_string
    acc = 0
    for i in range(0,len(element_exists)) :
        acc += element_exists[i]
        element_exists[i] = acc
    permutation = []
    for i in range(0,len(input_string_numbers)) :
        curr = abs(input_string_numbers[i])
        curr += element_exists[curr]

        if input_string_numbers[i] < 0 :
            permutation.append(-curr)
        else :
            permutation.append(curr)

    n = len(permutation) - 2
    position    = [-1 for i in range(0, n+2)]
    #sign        = [-1 for i in range(0, n+2)]


    for i in range(1, n+2) :
        position[abs(permutation[i])] = i
    #    sign    [abs(permutation[i])] = permutation[i] / abs(permutation[i])

    ## 1 if the gray edge i,-(i+1) was never used.
    gray_available     = [1 for i in range(0, n+1)]
    #black_available    = [1 for i in range(0, n+1)]

    cycles = []

    for i in range(0, n+1) : 
        if gray_available[i] :
            start     = i
            cycle = [start]

            end   = start
            positive  = True
            
            while True :
                ## Will be used later, it says if after walking through
                ## the black edge we are in the right or in the left
                is_vertex_left = None

                if positive :
                    ## Gray edge: we are looking for the edge ( end,-(end+1) )
                    gray_available[end] = gray_available[end] - 1
                    end = end + 1
                    cycle.append(end)

                    ## Black edge: we are at the vertex -end.
                    if permutation[position[end]] > 0 :
                        # If the sign in that position is positive, than
                        # -end is in the left (cycle graph)                    
                        end = abs(permutation[position[end]-1])
                        is_vertex_left = False
                    
                    else :
                        # If the sign in that position is negative, than
                        # -end is in the right (cycle graph)
                        end = abs(permutation[position[end]+1])
                        is_vertex_left = True
                else :
                    ## Gray edge: we are looking for the edge ( -end, end-1  )
                    end = end - 1                                 ##  Note we swapped
                    gray_available[end] = gray_available[end] - 1 ##  these lines
                    cycle.append(end)

                    #### Black edge: we are at the vertex +end.
                    if permutation[position[end]] > 0 :
                        # If the sign in that position is positive, than
                        # +end is in the right (cycle graph)
                        end = abs(permutation[position[end]+1])
                        is_vertex_left = True
                    else : 
                        # If the sign in that position is negative, than
                        # +end is in the left (cycle graph)
                        end = abs(permutation[position[end]-1])
                        is_vertex_left = False
                        
                if end == start :
                    break
                else :
                    cycle.append(end)
                    
                    if is_vertex_left :
                        if permutation[position[end]] < 0 :
                            positive = True
                        else :
                            positive = False
                    else :                    
                        if permutation[position[end]] < 0 :
                            positive = False
                        else :
                            positive = True
            cycles.append(cycle)

    int_position = get_position(permutation)
    canonicals = []

    for cycle in cycles :
        canonicals.append(canonical_representation(cycle, int_position))

    return(canonicals, wgray, wblack)


## This main function expects three lists as input (separated by spaces):
##     (i) a comma-separated list with integer numbers. The number 0 is considered 
##          an alpha that an indel will remove. Any other number must be unique, 
##          disregarding their signs.
##    (ii) a comma-separated list of non-negative integers with one more element
##          than list in (i), it represents intergenic sizes of the input genome
##   (iii) a comma-separated list of non-negative integers, it represents intergenic
##          sizes of the target genome

if __name__ == '__main__':
    seconds = time.time()
    permutation = eval("[%s]" % sys.argv[1])
    wblack = eval("[%s]" % sys.argv[2])
    wgray  = eval("[%s]" % sys.argv[3])

    # Use is_3approx for the algorithm published at AlCoB'2021 (preliminary version of the paper): Reversal Distance on Genomes with Different Gene Content and Intergenic Regions Information
    # The default version is the 2.5-approximation published at IEEE/ACM Transactions on Computational Biology and Bioinformatics
    if len(sys.argv) == 5 :
        is_3approx = sys.argv[4] == '3'
    else :
        is_3approx = False

    # print("is_3approx", is_3approx)
    final_length = len(wgray)

    config, grayw, blackw = construct_str_cycle(permutation, wgray, wblack)
    sort = Intergenic_Rev(config, grayw, blackw, final_length)
    sort.sort(seconds, is_3approx)

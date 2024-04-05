import copy

class Probability():
    """ 单个子公式情况 """
    def __init__(self, sat=False, st=None, operator=None, st_list =None, P_list=None, k_now=None):
        self.sat = sat  # satisfied
        self.start_time = st  # 记录目前该子公式在判断的Phi是哪个st开始的
        if k_now == None:
            self.k = None
        else:
            self.k = k_now-1  # 记录这个子公式的“当前时间”或“最终结束时间”，应该等于结束时的st+内层那个st的Phi的k，在开始前k都会为None，即k并不是从0开始的，而应该是从effctive[0]开始的
        #  现在我要改这个东西，在定义Probability的时候必须传进来一个k_now为"当前时间"，这个子公式里的所有子公式的k一定小于这个k_now，最大为k_now-1，
        #  因为这个有延迟性，你现在反映的结果一定是"上一个时刻"的状态"造成"的
        #  我现在把这个k存成k_now-1，如果这个P还没结束，那这个k就等于k_now-1，如果已经结束了，那就会<=k_now-1(取等的情况是上一时刻刚刚使其结束)
        self.P_list = P_list  # 对于G来说存的是里边的Phi的连续排布的[每个st的P_Phi们]，对于U来说存的是一前一后的[[每个st的P_Phi们], [每个st的P_Phi们]]
        self.operator = operator  # 这个应该有俩，分别是G，U
        self.st_list = st_list
        # print(self.st_list)
        if operator == 'G':
            self.self_check_G()
        elif operator == 'U':
            self.self_check_U()

    # def __repr__(self):
    #     if self.sat == True:
    #         # return 'T'
    #         return f'T({self.start_time})'
    #     elif self.sat == False:
    #         # return 'F'
    #         return f"F({self.start_time})"
    #     elif self.sat == 'violated':
    #         return f"V({self.start_time})"
    #     else:
    #         return 'aaabbbccc'
    # def __repr__(self):
    #     if self.sat == True:
    #         # return 'T'
    #         return f'T(st={self.start_time},k={self.k})({self.P_list})'
    #     elif self.sat == False:
    #         # return 'F'
    #         return f"F(st={self.start_time},k={self.k})({self.P_list})"
    #     elif self.sat == 'violated':
    #         return f"V(st={self.start_time},k={self.k})({self.P_list})"
    #     else:
    #         return 'aaabbbccc'
    def __repr__(self):
        if self.sat == True:
            # return 'T'
            return f'T(k={self.k})({self.P_list})'
        elif self.sat == False:
            # return 'F'
            return f"F(k={self.k})({self.P_list})"
        elif self.sat == 'violated':
            return f"V(k={self.k})({self.P_list})"
        else:
            return 'aaabbbccc'
    # def __repr__(self):
    #     if self.sat == True:
    #         return f'T(st={self.start_time},k={self.k})'
    #     elif self.sat == False:
    #         return f"F(st={self.start_time},k={self.k})"
    #     elif self.sat == 'violated':
    #         return f"V(st={self.start_time},k={self.k})"
    #     else:
    #         return f'aaabbbccc({self.P_list})'

    def is_equal(self, a):
        if self.operator != a.operator or self.sat != a.sat or self.start_time != a.start_time or self.st_list != a.st_list or len(self.P_list) != len(a.P_list):
            return False
        if self.operator == 'G':
            for i in range(len(self.P_list)):
                if not self.P_list[i].is_equal(a.P_list[i]):
                    return False
        elif self.operator == 'U':
            for i in range(len(self.P_list[0])):
                if not self.P_list[0][i].is_equal(a.P_list[0][i]):
                    return False
            for i in range(len(self.P_list[1])):
                if not self.P_list[1][i].is_equal(a.P_list[1][i]):
                    return False
        return True

    def self_check_G(self):
        #  对于没开始的(以及刚开始第一步的)，sat为F，st为a，k为None
        self.sat = False
        self.start_time = self.st_list[0]
        for i in range(len(self.P_list)):
            if self.P_list[i].sat == "violated":
                self.sat = "violated"
                self.start_time = self.st_list[i]
                self.k = self.st_list[i] + self.P_list[i].k
                break
            elif self.P_list[i].sat == True:
                if i != len(self.st_list) - 1:
                    self.sat = False
                    self.start_time = self.st_list[i]+1
                    self.k = self.st_list[i]+self.P_list[i].k
                else:
                    self.sat = True
                    self.start_time = self.st_list[-1]
                    self.k = self.st_list[i] + self.P_list[i].k
            elif self.P_list[i].sat == False:
                if self.P_list[i].k == None:  # 说明这个往后的都还没开始
                    break
                else:  # 说明是一个真的F，而不是一个没开始的
                    self.sat = False
                    self.start_time = self.st_list[i]
                    self.k = self.st_list[i] + self.P_list[i].k
                    break

    def self_check_U(self):
        #  之前那个已经用不了了，因为U的存法变了，Uqian不是一个P而是P_Phi的列表了
        #  没开始的情况
        if self.P_list[0][0].k == None:
            self.sat = False
            self.start_time = self.st_list[0]
            return 0
        Uhou_all_die = False
        if len(self.P_list[1]) == len(self.st_list):
            # 如果Uhou已经V完了，那必死了，但是这个k怎么确定呢？,是否一定是Uhou全V的那一刻呢？暂且先认为是吧    感觉不一定...
            # 确实不对，我觉得这个死法得记下来，然后继续去判断后边的死法，看看哪个先死，再做判断
            Uhou_all_die = True
            if len(self.P_list[1]) == len(self.st_list):
                for p in self.P_list[1]:
                    if p.sat != "violated":
                        Uhou_all_die = False
                        break
            if Uhou_all_die:
                k_Uhou_all_die = self.st_list[-1] + self.P_list[1][-1].k
        # 开始了，那就逐个st往后找看状态
        for i in range(min(len(self.P_list[0]),len(self.P_list[1]))):
            if self.P_list[0][i].sat == True:
                if self.P_list[1][i].sat == True:
                    self.sat = True
                    self.start_time = self.st_list[i]
                    self.k = self.st_list[i] + max(self.P_list[0][i].k, self.P_list[1][i].k)
                    return 0
                elif self.P_list[1][i].sat == "violated":
                    if i != len(self.st_list) - 1:
                        continue
                    else:  # 如果我是Uhou最后一个且我还是V了，那这个U也V了
                        self.sat = "violated"
                        self.start_time = self.st_list[i]
                        self.k = self.st_list[i] + self.P_list[1][i].k
                elif self.P_list[1][i].sat == False:
                    self.sat = False  # 只要有False就不用管k,k默认存的就是最新的
                    self.start_time = self.st_list[i]
                    return 0
            elif self.P_list[0][i].sat == "violated":
                self.sat = "violated"
                self.start_time = self.st_list[i]
                if i != 0:
                    self.k = max(self.st_list[i]+self.P_list[0][i].k, self.st_list[i-1]+self.P_list[1][i-1].k)
                #  是Uqian的V宣告了死亡，还是Uqian早就V了，但是还在等上一个看有没有可能True救一下，结果上一个死了，那就是上一个死时宣告死亡
                else:  # 如果i是0，就是Uqian一上来就死了，那必是Uqian的死宣告了死亡
                    #  等下，是不是还得跟下边V完了比比先后，万一下边V完了上边还没死怎么办
                    self.k = self.st_list[i] + self.P_list[0][i].k
                if Uhou_all_die:
                    if self.k > k_Uhou_all_die:
                        self.k = k_Uhou_all_die
                return 0
            elif self.P_list[0][i].sat == False:
                if Uhou_all_die:
                    self.sat = "violated"
                    self.k = k_Uhou_all_die
                    return 0
                self.sat = False
                self.start_time = self.st_list[i]
                return 0

class Probability_Phi():
    """ 一个很多个子公式并列的Phi的情况 """
    # 这个东西一般外层会套个G或者U之类的然后开始连续排布，不过连续排布排到哪一个st的时候是什么了，这个st是存在外边那个Probability里的，不在这存
    # 如果P是一个[]，没开始的sat为F(0)，开始之后的sat只有T(0)和V(0)两种情况
    def __init__(self, sat=False, k=None, P_list=None, H=None):
        self.sat = sat  # satisfied
        self.k = k  # 这个Phi在第k步(相对于其st的，默认是从0开始的，如果是从某st开始的那对于外边的那层来说时间是st+k)为T/F/V，如果是[]必取0
        #  如果sat是T，那k是所有子公式里st+k'(子公式内层P_Phi的k)最大的；如果sat是V，那k是所有子公式里st+k'最小的
        self.P_list = P_list  # 有几个子公式用∧并列，就是个长度为几的列表，每个元素是一个Probability类，即使只有一个子公式也要用这个处理
        #  如果是一个[]，那P_list就是None了
        self.H = H  # 只有P_list是None的时候这个才有值，这个存最底层Phi是[]的时候的范围H
        if self.P_list != None:
            self.self_check()

    # def __repr__(self):
    #     if self.P_list == None:
    #         if self.sat == True:
    #             return f"T_({self.k})"
    #         elif self.sat == False:
    #             return f"F_({self.k})"
    #         elif self.sat == "violated":
    #             return f"V_({self.k})"
    #     else:
    #         if self.sat == True:
    #             return f"T_({self.k})({self.P_list})"
    #         elif self.sat == False:
    #             return f"F_({self.k})({self.P_list})"
    #         elif self.sat == "violated":
    #             return f"V_({self.k})({self.P_list})"
    def __repr__(self):
        if self.sat == True:
            return f"T_({self.k})"
        elif self.sat == False:
            return f"F_({self.k})"
        elif self.sat == "violated":
            return f"V_({self.k})"
    # def __repr__(self):
    #     if self.P_list == None:
    #         if self.sat == True:
    #             return 'T'
    #         elif self.sat == False:
    #             return 'F'
    #         elif self.sat == "violated":
    #             return 'V'
    #     else:
    #         return str(self.P_list)
    # def __repr__(self):
    #     if self.P_list == None:
    #         if self.sat == True:
    #             return f"T(k={self.k})"
    #         elif self.sat == False:
    #             return f"F(k={self.k})"
    #         elif self.sat == "violated":
    #             return f"V(k={self.k})"
    #     else:
    #         return str(self.P_list)

    def is_equal(self, a):
        if self.P_list != None:  # 如果这不是一个[]
            if self.sat != a.sat or self.k != a.k or len(self.P_list) != len(a.P_list):
                return False
            for i in range(len(self.P_list)):
                if not self.P_list[i].is_equal(a.P_list[i]):
                    return False
        else:
            if self.sat != a.sat:
                return False
        return True

    def self_check(self):
        # 根据P_list设置自己的sat和k
        k_list = []
        if self.P_list != None:  # 不是None说明不是[]，是[]的话就不用设置。
            # 首先检查是不是全都没开始，全没开始认为这个P_Phi也没开始
            is_not_start = True
            for i in range(len(self.P_list)):
                if self.P_list[i].k != None:
                    is_not_start = False
            if is_not_start:
                self.sat = False
                self.k = None  # 如果都没开始
                return 0
            # 然后看这个P_Phi死没死，有一个死了就死了，且死亡时间是最早那个死的时间
            is_violated = False
            for i in range(len(self.P_list)):
                if self.P_list[i].sat == "violated":
                    is_violated = True
                    k_list += [self.P_list[i].k]
            if is_violated:
                self.sat = "violated"
                self.k = min(k_list)
                return 0
            # 这里往下说明没有violated，P_Phi里的P不是T就是F，全是T就是T，有F就是F，k取所有里边最大的
            is_False = False
            for i in range(len(self.P_list)):
                if self.P_list[i].sat == False:  # ???那么朋友我有一个问题，如果这个F是F(None)未开始，你下边那个k_list怎么办???
                    is_False = True
                    if self.P_list[i].k != None:  # 万一已经开始的全True了，剩下的都是还没开始的，怎么办？取None吗？也不能取所有True里最大的啊，已经过时了，是不是需要在构造时引入当前的k了？
                        # 现在已经改了，k从0开始，上边这种情况不存在了，因为所有的子公式都会同时开始，因为他们是处在同一层的，所以共享同一个时间轴，开始了就都开始了
                        k_list += [self.P_list[i].k]  # 其实这一步都多余，因为所有还是False的P的k肯定是相等的，都还在更新，所以都同k
            if is_False:
                self.sat = False
                self.k = max(k_list)
                return 0
            # 这里往下说明没有False和violated，全是True，那这个P_Phi也为True，且为True的时间应该是这里边最晚为True的时间(在此之前算F)
            self.sat = True
            k_list = []
            for i in range(len(self.P_list)):
                k_list += [self.P_list[i].k]
            self.k = max(k_list)

class Phi():
    """ 一个可嵌套的STL公式 """
    # 构造方法：
    def __init__(self, a, b, operator, phi, phi_1=[None]):  # 注意对U是先传后边再传前边，输入要按顺序来，G的phi_1虽没有也要给个None
        self.a = a  # 开始时刻
        self.b = b  # 结束时刻
        self.operator = operator  # 'U' or 'G'  这个U是按学姐论文的U'定义的
        self.phi = phi  # 后边那个
        self.phi_1 = phi_1  # 前边那个，仅U有
        self.Phi_list = []  # 当该Phi是好几个Phi的合的时候，用一个这个存储每一个单独的Phi

        if len(self.a) > 1:  # 如果是好几个并列的Phi组成的Phi，分别存储一下每个Phi(感觉有用)
            for i in range(len(self.a)):
                self.Phi_list += [Phi([self.a[i]], [self.b[i]], [self.operator[i]], [self.phi[i]], [self.phi_1[i]])]

    # 重写print
    def __repr__(self):
        prt = ''
        for i in range(0,len(self.a)):
            if self.operator[i] == 'U':
                prt += f"({self.phi_1[i]}){self.operator[i]}[{self.a[i]},{self.b[i]}]({self.phi[i]})"
            elif self.operator[i] == 'G':
                prt += f"{self.operator[i]}[{self.a[i]},{self.b[i]}]({self.phi[i]})"
            if i != len(self.a)-1:
                prt += '∧'
        return prt

    # 检查一个序列是否满足此公式
    def check(self, signal):  # 在嵌套时，只需要每次传给下一个内层的信号序列都是从我的有效区间起点开始的信号切片，即可实现”相对“区间，天才！
        for i in range(0, len(self.a)):
            if self.operator[i] == 'G':
                if type(self.phi[i]) == type([]):
                    for x in signal[self.a[i]:self.b[i]+1]:
                        if x not in self.phi[i]:
                            return False
                elif type(self.phi[i]) == type(self):
                    for i1 in range(self.a[i],self.b[i]+1):
                        if not self.phi[i].check(signal[i1:]):
                            return False

            elif self.operator[i] == 'U':
                satisfied = False
                if type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type([]):
                    for i1 in range(self.a[i],self.b[i]+1):
                        if (signal[i1] in self.phi_1[i]) and (signal[i1] in self.phi[i]):
                            satisfied = True
                            break
                        elif signal[i1] in self.phi_1[i]:
                            pass
                        else:
                            return False
                    if satisfied == False:
                        return False
                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type(self):
                    for i1 in range(self.a[i],self.b[i]+1):
                        if self.phi_1[i].check(signal[i1:]) and self.phi[i].check(signal[i1:]):
                            satisfied = True
                            break
                        elif self.phi_1[i].check(signal[i1:]):
                            pass
                        else:
                            return False
                    if satisfied == False:
                        return False
                elif type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type(self):
                    for i1 in range(self.a[i],self.b[i]+1):
                        if (signal[i1] in self.phi_1[i]) and self.phi[i].check(signal[i1:]):
                            satisfied = True
                            break
                        elif (signal[i1] in self.phi_1[i]):
                            pass
                        else:
                            return False
                    if satisfied == False:
                        return False
                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type([]):
                    for i1 in range(self.a[i],self.b[i]+1):
                        if self.phi_1[i].check(signal[i1:]) and (signal[i1] in self.phi[i]):
                            satisfied = True
                            break
                        elif self.phi_1[i].check(signal[i1:]):
                            pass
                        else:
                            return False
                    if satisfied == False:
                        return False

        return True

    # 计算一个公式的(最大)有效区间(对于G来说就是有效区间，对于U来说是最大有效区间)  输出[start,end]
    def effective_horizon(self):
        start_list = []
        end_list = []
        for i in range(0, len(self.a)):
            if self.operator[i] == 'G':
                if type(self.phi[i]) == type([]):  # 其实如果phi是一个[]，相当于是一个作用范围为[0,0]的Phi，可以看成是两个+0
                    start_list += [self.a[i]]
                    end_list += [self.b[i]]
                elif type(self.phi[i]) == type(self):
                    start_list += [self.a[i]+self.phi[i].effective_horizon()[0]]
                    end_list += [self.b[i]+self.phi[i].effective_horizon()[1]]

            elif self.operator[i] == 'U':  # a要加两边最小的a，一旦两边有一个是[]，相当于是0，所以+0，但b要加最大的b
                if type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type([]):
                    start_list += [self.a[i]]
                    end_list += [self.b[i]]
                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type(self):
                    start_list += [self.a[i] + min([self.phi[i].effective_horizon()[0], self.phi_1[i].effective_horizon()[0]])]
                    end_list += [self.b[i] + max([self.phi[i].effective_horizon()[1], self.phi_1[i].effective_horizon()[1]])]
                elif type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type(self):
                    start_list += [self.a[i]]
                    end_list += [self.b[i] + self.phi[i].effective_horizon()[1]]
                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type([]):
                    start_list += [self.a[i]]
                    end_list += [self.b[i] + self.phi_1[i].effective_horizon()[1]]
        # print(start_list)
        # print(end_list)
        start = min(start_list)
        end = max(end_list)
        return [start, end]

    # 判断什么时候必在潜在索引集里(最早可能结束的时间及在此之前的时间)  输出[0,1,2,...,最早结束时间]
    def in_potential(self):  # 悟了，其实“必在潜在索引集”的时间就是“可能的最早结束的时间”以及在此之前的时间
        time_list = []  # 用于记录必在潜在索引集里的对应的时间
        for i1 in range(0,self.effective_horizon()[0]):  # 没开始的都在里边
            time_list += [i1]
        # print(time_list)
        every_time_list = []  # 用于记录∧的每一个的必在潜在索引集里的时间，最后取并集（只要有一个必在，整个就必在）
        for i in range(0,len(self.a)):
            if self.operator[i] == 'G':  # G其实就相当于很多个∧，对他们都取并集就对了
                if type(self.phi[i]) == type([]):  # 如果phi是一个[]，相当于是一个作用范围为[0,0]的Phi，并集就是每个列出来
                    every_time_list += [list(range(self.a[i], self.b[i]+1))]
                elif type(self.phi[i]) == type(self):
                    G_time_list = []
                    for i1 in range(self.a[i], self.b[i]+1):
                        linshi = []
                        for i2 in self.phi[i].in_potential():
                            linshi += [i1 + i2]
                        G_time_list = list(set(G_time_list) | set(linshi))
                    # print(G_time_list)
                    every_time_list += [G_time_list]
            elif self.operator[i] == 'U':  # U之所以只有第一个一定在潜在集里是因为可能一上来就同时都满足了，所以U的潜在集就是前后潜在集的并集
                start = self.a[i]
                if type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type([]):
                    every_time_list += [[start]]
                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type(self):
                    linshi_1 = []
                    linshi = []
                    for i1 in self.phi_1[i].in_potential():
                        linshi_1 += [i1 + start]
                    for i1 in self.phi[i].in_potential():
                        linshi += [i1 + start]
                    U_time_list = list(set(linshi) | set(linshi_1))
                    every_time_list += [U_time_list]
                elif type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type(self):
                    linshi = []
                    for i1 in self.phi[i].in_potential():
                        linshi += [i1 + start]
                    U_time_list = list(set(linshi) | set([start]))
                    every_time_list += [U_time_list]
                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type([]):
                    linshi_1 = []
                    for i1 in self.phi_1[i].in_potential():
                        linshi_1 += [i1 + start]
                    U_time_list = list(set([start]) | set(linshi_1))
                    every_time_list += [U_time_list]
        final_time_list = []
        # print(time_list)
        # print(every_time_list)
        for i in range(0,len(every_time_list)):
            final_time_list = list(set(final_time_list)|set(every_time_list[i]))
        time_list = list(set(final_time_list)|set(time_list))
        return time_list

    # 判断什么时候开始一个式子可以被判定为violated了，返回一个列表，表示每个子公式的最早可死时间
    def can_die_time_list(self):  # 一定注意这个时间和effective_horizon[0]并无绝对关系，在这里边不能引用effective_horizon
        can_die_time_list = []
        for i in range(0, len(self.a)):
            if self.operator[i] == 'G':   # 第一个可以死的时候就可以死了
                if type(self.phi[i]) == type([]):  # 其实如果phi是一个[]，相当于是一个作用范围为[0,0]的Phi，这一步要判断，下一步才能死，所以+1
                    can_die_time = self.a[i]+1
                    can_die_time_list += [can_die_time]
                elif type(self.phi[i]) == type(self):
                    can_die_time = self.a[i] + min(self.phi[i].can_die_time_list())  # 取min，∧之间有一个能死就都死了
                    can_die_time_list += [can_die_time]

            elif self.operator[i] == 'U':  # 前边能第一个能死，或者后边能死完，哪个先哪个作为能死时间
                if type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type([]):
                    can_die_time = self.a[i]+1
                    can_die_time_list += [can_die_time]
                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type(self):
                    can_die_time = min([self.a[i]+min(self.phi_1[i].can_die_time_list()), self.b[i]+min(self.phi[i].can_die_time_list())])
                    can_die_time_list += [can_die_time]
                elif type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type(self):
                    can_die_time = self.a[i] + 1
                    can_die_time_list += [can_die_time]
                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type([]):
                    can_die_time = min([self.a[i]+min(self.phi_1[i].can_die_time_list()), self.b[i]+1])
                    can_die_time_list += [can_die_time]

        return can_die_time_list

    def pailiezuhe(self, original_list_k, num, linshi_list=[], flag=0):
        result = []
        if flag < (num-1):
            for i in range(len(original_list_k[flag])):
                linshi_list_this = linshi_list + [original_list_k[flag][i]]
                result += self.pailiezuhe(original_list_k, num, linshi_list_this, flag+1)
        else:
            for i in range(len(original_list_k[flag])):
                linshi_list_this = linshi_list + [original_list_k[flag][i]]
                result += [linshi_list_this]
        return result

    def pailiezuhe_not_v(self, original_list_k, num, linshi_list=[], flag=0):
        # 出现有V的就不存，只留T和F的，用来只保留能活下去的情况
        result = []
        if flag < (num-1):
            for i in range(len(original_list_k[flag])):
                if original_list_k[flag][i].sat == "violated":
                    continue
                linshi_list_this = linshi_list + [original_list_k[flag][i]]
                result += self.pailiezuhe_not_v(original_list_k, num, linshi_list_this, flag+1)
        else:
            for i in range(len(original_list_k[flag])):
                if original_list_k[flag][i].sat == "violated":
                    continue
                linshi_list_this = linshi_list + [original_list_k[flag][i]]
                result += [linshi_list_this]
        return result

    def pailiezuhe_G(self, original_list_k, num, linshi_list=[], flag=0):
        # 传进来的是 [[k时a开始的P_Phi的各种可能],[k时a+1开始的P_Phi的各种可能],...,[k时b开始的P_Phi的各种可能]]
        result = []
        if flag < (num-1):
            for i in range(len(original_list_k[flag])):
                if original_list_k[flag][i].k == None:
                    if flag == 0:  # 第一个都没开始的时候存None，第一个开始之后就不再存None了
                        linshi_list_this = linshi_list + [original_list_k[flag][i]]
                        result += [linshi_list_this]
                    else:
                        linshi_list_this = linshi_list
                        result += [linshi_list_this]
                elif original_list_k[flag][i].sat != "violated":
                    linshi_list_this = linshi_list + [original_list_k[flag][i]]
                    result += self.pailiezuhe_G(original_list_k, num, linshi_list_this, flag+1)
                else:
                    linshi_list_this = linshi_list + [original_list_k[flag][i]]
                    result += [linshi_list_this]
        else:
            for i in range(len(original_list_k[flag])):
                if original_list_k[flag][i].k == None:
                    if flag == 0:  # 第一个都没开始的时候存None，第一个开始之后就不再存None了
                        linshi_list_this = linshi_list + [original_list_k[flag][i]]
                        result += [linshi_list_this]
                    else:
                        linshi_list_this = linshi_list
                        result += [linshi_list_this]
                else:
                    linshi_list_this = linshi_list + [original_list_k[flag][i]]
                    result += [linshi_list_this]
        return result

    def pailiezuhe_Uhou_over(self, Uqian, original_list, U_st_list, num, k, jicheng=None, linshi_list=[], flag=0):
        # 用来处理Uhou提前完成了，在Uqian完成时需排列组合Uhou在这期间的各种排列组合情况 条件为 st+k<=k
        result = []
        k_max = k  # 这个传进来的好像已经是-1的了
        if flag < (num - 1):
            for i in range(len(original_list[flag])):
                if original_list[flag][i].k == None:  # 如果这个还没开始那就在这里停下就好了,后边肯定都没开始，i也只有这一个的，不用break或者continue了
                    linshi_list_this = linshi_list  # 也不用存这个None了，因为只要进了Uhou，flag就肯定不是0了，至少是1
                    p = Probability(None, None, 'U', U_st_list, [Uqian, linshi_list_this], k+1)
                    result += [p]
                else:  # 到这说明这个开始了，那要先检查是否满足连续条件，再检查k是否满足要求
                    is_cuowei = self.is_cuowei(jicheng, original_list[flag][i])
                    if not is_cuowei:
                        continue  # 不满足连续条件直接走
                    if U_st_list[flag]+original_list[flag][i].k <= k: # 这个既满足连续条件也满足k的条件，留下，继续往后找
                        linshi_list_this = linshi_list + [original_list[flag][i]]
                        result += self.pailiezuhe_Uhou_over(Uqian, original_list, U_st_list, num, k, original_list[flag][i], linshi_list_this, flag + 1)
                    else:  # 这个比k大了，那这个就不留了，把之前存的存个p就行了
                        linshi_list_this = linshi_list
                        p = Probability(None, None, 'U', U_st_list, [Uqian, linshi_list_this], k+1)
                        result += [p]
        else:
            for i in range(len(original_list[flag])):
                if original_list[flag][i].sat == "violated":  # 这个出现说明可能早就死了，如果出现了要跟现在时间对比一下，如果是早死了就不要了
                    all_violated = True
                    for p_zhiqiande in linshi_list:
                        if p_zhiqiande.sat != "violated":
                            all_violated = False
                            break
                    if all_violated:
                        k_over = U_st_list[flag] + original_list[flag][i].k
                        if k_over != k_max:
                            continue
                if original_list[flag][i].k == None:  # 如果这个还没开始那就在这里停下就好了,后边肯定都没开始，i也只有这一个的，不用break或者continue了
                    linshi_list_this = linshi_list  # 也不用存这个None了，因为只要进了Uhou，flag就肯定不是0了，至少是1
                    p = Probability(None, None, 'U', U_st_list, [Uqian, linshi_list_this], k+1)
                    result += [p]
                else:  # 到这说明这个开始了，那要先检查是否满足连续条件，再检查k是否满足要求
                    is_cuowei = self.is_cuowei(jicheng, original_list[flag][i])
                    if not is_cuowei:
                        continue  # 不满足连续条件直接走
                    if U_st_list[flag] + original_list[flag][i].k <= k:  # 这个既满足连续条件也满足k的条件，最后一个了，留下，结束
                        linshi_list_this = linshi_list + [original_list[flag][i]]
                        p = Probability(None, None, 'U', U_st_list, [Uqian, linshi_list_this], k+1)
                        result += [p]
                    else:  # 这个比k大了，那这个就不留了，把之前存的存个p就行了
                        linshi_list_this = linshi_list
                        p = Probability(None, None, 'U', U_st_list, [Uqian, linshi_list_this], k+1)
                        result += [p]
        return result

    def pailiezuhe_U1(self, Uqian, Uhou_list_k_original, U_st_list, num, k, jicheng=None, linshi_list=[], flag=0):
        #  希望它能处理更复杂的U的情况
        #  注意传进来的k得是是(k_now-1)了(即现在能检测到的最新的k)，这样里边的处理就不用再额外-1了
        #  算了我还是直接在这处理一下吧
        k_max = k-1
        #  传进来的是Uqian的一个确定的情况[a的P_Phi,a+1的P_Phi,...,b的P_Phi] 当然实际上不一定到b，比如前边死了就没存后边的了，或者后边可能有还没开始的没存
        #  以及Uhou后边所有有可能的情况[[a时所有可能的情况],[a+1时所有可能的情况],...,[b时所有可能的情况]] 这个肯定到b
        #  但是要注意Uhou排列的时候，遇到未开始的就存一个不存了，前后存的时候要检查是否满足连续条件if_cuowei
        result = []
        if flag < (num - 1):
            if Uqian[flag].sat == True:
                for i in range(len(Uhou_list_k_original[flag])):
                    if jicheng != None:  # 首先得检查连续条件
                        is_cuowei = self.is_cuowei(jicheng, Uhou_list_k_original[flag][i])
                        if not is_cuowei:
                            continue
                    if Uhou_list_k_original[flag][i].sat == True:  # Uqian和Uhou在这个st同为T，这个U在这里满足了
                        linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                        k_self = max(Uqian[flag].k, Uhou_list_k_original[flag][i].k)  # 虽然对于[]U[]的情况这俩都是0...
                        k_over = U_st_list[flag] + k_self  # 完成时的k，如果不等于k_max的话就舍弃(因为说明是之前结束的)
                        if k_over != k_max:
                            continue
                        # 等于的话说明是现在结束的，开始找排列组合
                        Uqian_this = []
                        Uhou_this = linshi_list_this
                        if Uqian[flag].k > Uhou_list_k_original[flag][i].k:  # 是由Uqian结束的，那Uqian只存这个以及<的,Uhou存<=的(但是是不是也可以只存一堆=里的第一个)
                            # for j in range(flag+1): # 这个以及<的其实就是[0,flag]的
                            #     Uqian_this += [Uqian[j]]
                            Uqian_this = Uqian[0:flag+1]
                            result += self.pailiezuhe_Uhou_over(Uqian_this, Uhou_list_k_original, U_st_list, num, k_over, Uhou_list_k_original[flag][i], linshi_list_this, flag + 1)
                            # print(k_over)
                            # print(self.pailiezuhe_Uhou_over(Uqian_this, Uhou_list_k_original, U_st_list, num, k_over, Uhou_list_k_original[flag][i], linshi_list_this, flag + 1))
                        elif Uqian[flag].k < Uhou_list_k_original[flag][i].k: # 是由Uhou结束的，那Uhou只存这个以及<的,Uqian存<=的(但是是不是也可以只存一堆=里的第一个)
                            for j in range(len(Uqian)):
                                if U_st_list[j] + Uqian[j].k <= k:
                                    Uqian_this += [Uqian[j]]
                                else:
                                    break  # 因为后边的k肯定大于等于这个，所以有一个大于的后边就不管了
                            p = Probability(True, U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k+1)
                            result += [p]
                        elif Uqian[flag].k == Uhou_list_k_original[flag][i].k: # 同时结束，都只取当前的就行
                            Uqian_this = Uqian[0:flag + 1]
                            p = Probability(True, U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k+1)
                            result += [p]

                    elif Uhou_list_k_original[flag][i].sat == "violated":  # st的Uqian满足Uhou没满足，继续Until下去了
                        linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                        result += self.pailiezuhe_U1(Uqian, Uhou_list_k_original,  U_st_list, num, k, Uhou_list_k_original[flag][i], linshi_list_this, flag + 1)

                    elif Uhou_list_k_original[flag][i].sat == False:  # st的Uqian满足了，Uhou还不确定能不能满足，Uhou存到这就行了，k一定是最新的k，然后看Uqian存到哪
                        # 不过还有一种可能，是这个Uhou还没开始，那Uhou也只存到这就行了，那Uqian怎么找？答：一直找到没开始的为止，因为k一定是最新的k，所以除了没开始的k都<=现在的k
                        linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                        for j in range(len(Uqian)):
                            if Uqian[j].k != None:
                                Uqian_this += [Uqian[j]]
                            else:
                                break  # 因为后边的k肯定大于等于这个，所以有一个大于的后边就不管了
                        p = Probability(None, None, 'U', U_st_list, [Uqian_this, linshi_list_this], k)
                        result += [p]

            elif Uqian[flag].sat == "violated":  # 这个U在这个k已经死了，且这肯定也是Uqian的最后一个(因为Uqian的存法是遇V就停)，看看Uhou怎么排就行了
                k_over = U_st_list[flag] + Uqian[flag].k
                # print(f"V{k_over}")
                # print(f"max{k_max}")
                if k_over != k_max:  # 如果不是刚刚死的，那就不管
                    return []
                Uqian_this = Uqian[0:flag + 1]
                for i in range(len(Uhou_list_k_original[flag])):
                    if jicheng != None:
                        is_cuowei = self.is_cuowei(jicheng, Uhou_list_k_original[flag][i])
                        if not is_cuowei:
                            continue
                    linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                    if Uhou_list_k_original[flag][i].k == None: # 这种情况只有一种情况就是这是第一个Uqian上来就死了，Uhou还没开始，否则但凡第一个Uqian是T，后边没开始都会等后边的
                        p = Probability("violated", U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k_over+1)
                        result += [p]
                    elif Uqian[flag].k > Uhou_list_k_original[flag][i].k:  # 是由Uqian结束的，那Uqian只存这个以及<的,Uhou存<=的(但是是不是也可以只存一堆=里的第一个)
                        result += self.pailiezuhe_Uhou_over(Uqian_this, Uhou_list_k_original, U_st_list, num, k_over, Uhou_list_k_original[flag][i], linshi_list_this, flag + 1)
                    elif Uqian[flag].k == Uhou_list_k_original[flag][i].k:  # 如果等于就都存一个算了，我也不知道这样好不好，但是应该不会影响情况的数量，规定以后都等于就只存一个
                        p = Probability("violated", U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k_over+1)
                        result += [p]
                    elif Uqian[flag].k < Uhou_list_k_original[flag][i].k:  # 这种情况是，Uqian早就死在了这V(st),在等我前边的Uhou有没有机会True一个救一下，可惜没有，于是到这了
                        # 能到这说明前边的Uhou都为violated，而我也是后来才到这，那其实真正宣判我死刑的时间不是这个k，而是我的上一个的violated的时间，这个也不用存了，存linshi_list就行
                        k_over = U_st_list[flag-1] + jicheng.k
                        p = Probability("violated", U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list], k_over+1)
                        result += [p]

            elif Uqian[flag].sat == False: # Uqian还不确定或者还没开始，那Uqian的k已经必定是最新的k了，Uqian存到这就行，后边一直排到没开始就行
                if Uqian[flag].k == None:  # !!!!!这其实是很要紧的一种情况，因为整个U开始之前就会走到这来，U开始前怎么存？
                    k = k
                    if flag == 0:  # 只有第一个就是None才存None
                        Uqian_this = Uqian[0:flag + 1]
                    else:
                        Uqian_this = Uqian[0:flag]
                else:
                    k = U_st_list[flag] + Uqian[flag].k + 1  # 这里和上边不一样了，在这里就加1，懒得再搞了
                    Uqian_this = Uqian[0:flag + 1]
                for i in range(len(Uhou_list_k_original[flag])):
                    if jicheng != None:
                        is_cuowei = self.is_cuowei(jicheng, Uhou_list_k_original[flag][i])
                        if not is_cuowei:
                            continue
                    linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                    if Uhou_list_k_original[flag][i].k == None:  # 这个Uhou还没开始，俩都不确定
                        # 现在这种情况只有两个同为None才可能发生了，因为他们俩st相同，开始了就肯定都开始了，直接传k不用+1没毛病
                        p = Probability(False, U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k)
                        result += [p]
                    else:
                        result += self.pailiezuhe_Uhou_over(Uqian_this, Uhou_list_k_original, U_st_list, num, k-1, Uhou_list_k_original[flag][i], linshi_list_this, flag + 1)

        else:  # 到这说明已经是Uqian和Uhou的最后一层了，是不是可以在这里先判断一下Uhou这里是不是V？
            for i in range(len(Uhou_list_k_original[flag])):
                if jicheng != None:
                    is_cuowei = self.is_cuowei(jicheng, Uhou_list_k_original[flag][i])
                    if not is_cuowei:
                        continue
                if Uhou_list_k_original[flag][i].sat == "violated":
                    k_over = U_st_list[flag] + Uhou_list_k_original[flag][i].k
                    if k_over != k_max:
                        continue
                    linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                    Uqian_this = Uqian
                    p = Probability('violated', U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k_over+1)
                    result += [p]
            #  不对，你就算在这上边把Uhou全V的情况处理了，不妨碍后边它还会出现啊，因为后边的 for i都是在if里边的
            #  哦哦哦哦哦，有了，我在这里处理完，后边的每个情况里再加一个，如果Uhou_list_k_original[flag][i].sat是V直接continue
            #  我去，天才！
            if Uqian[flag].sat == True:
                for i in range(len(Uhou_list_k_original[flag])):
                    if jicheng != None:  # 首先得检查连续条件
                        is_cuowei = self.is_cuowei(jicheng, Uhou_list_k_original[flag][i])
                        if not is_cuowei:
                            continue
                    if Uhou_list_k_original[flag][i].sat == "violated":  # 这个最上边已经处理过了
                        continue

                    if Uhou_list_k_original[flag][i].sat == True:  # Uqian和Uhou在这个st同为T，这个U在这里满足了
                        linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                        k_self = max(Uqian[flag].k, Uhou_list_k_original[flag][i].k)  # 虽然对于[]U[]的情况这俩都是0...
                        k_over = U_st_list[flag] + k_self  # 完成时的k，如果不等于k_max的话就舍弃(因为说明是之前结束的)
                        if k_over != k_max:
                            continue
                        # 等于的话说明是现在结束的，开始找排列组合
                        Uqian_this = Uqian
                        p = Probability(True, U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k_over+1)
                        result += [p]

                    elif Uhou_list_k_original[flag][i].sat == "violated":  # st的Uqian满足Uhou没满足，继续Until下去了
                        linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                        k_over = U_st_list[flag] + Uhou_list_k_original[flag][i].k  # 最后一个还是V时已经宣判死刑了
                        if k_over != k_max:  # 完成时的k，如果不等于k_max的话就舍弃(因为说明是之前结束的)
                            continue
                        Uqian_this = Uqian
                        p = Probability('violated', U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k_over+1)
                        result += [p]

                    elif Uhou_list_k_original[flag][i].sat == False:  # st的Uqian满足了，Uhou还不确定能不能满足，Uhou存到这就行了，k一定是最新的k，然后看Uqian存到哪
                        # 不过还有一种可能，是这个Uhou还没开始，那Uhou也只存到这就行了，那Uqian怎么找？答：一直找到没开始的为止，因为k一定是最新的k，所以除了没开始的k都<=现在的k
                        linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                        for j in range(len(Uqian)):
                            if Uqian[j].k != None:
                                Uqian_this += [Uqian[j]]
                            else:
                                break  # 因为后边的k肯定大于等于这个，所以有一个大于的后边就不管了
                        p = Probability(None, None, 'U', U_st_list, [Uqian_this, linshi_list_this])
                        result += [p]

            elif Uqian[flag].sat == "violated":  # 这个U在这个k已经死了，且这肯定也是Uqian的最后一个(因为Uqian的存法是遇V就停)，看看Uhou怎么排就行了
                k_over = U_st_list[flag] + Uqian[flag].k
                if k_over != k_max:
                    return []
                Uqian_this = Uqian[0:flag + 1]
                for i in range(len(Uhou_list_k_original[flag])):
                    if jicheng != None:
                        is_cuowei = self.is_cuowei(jicheng, Uhou_list_k_original[flag][i])
                        if not is_cuowei:
                            continue
                    if Uhou_list_k_original[flag][i].sat == "violated":  # 这个最上边已经处理过了
                        continue
                    linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                    if Uqian[flag].k >= Uhou_list_k_original[flag][i].k:  # 如果等于就都存一个算了，我也不知道这样好不好，但是应该不会影响情况的数量，规定以后都等于就只存一个
                        p = Probability("violated", U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k_over+1)
                        result += [p]
                    elif Uqian[flag].k < Uhou_list_k_original[flag][i].k:  # 这种情况是，Uqian早就死在了这V(st),在等我前边的Uhou有没有机会True一个救一下，可惜没有，于是到这了
                        # 能到这说明前边的Uhou都为violated，而我也是后来才到这，那其实真正宣判我死刑的时间不是这个k，而是我的上一个的violated的时间，这个也不用存了，存linshi_list就行
                        k = U_st_list[flag - 1] + jicheng.k
                        p = Probability("violated", U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list], k_over+1)
                        result += [p]

            elif Uqian[flag].sat == False:  # Uqian还不确定或者还没开始，那Uqian的k已经必定是最新的k了，Uqian存到这就行，后边一直排到没开始就行
                #  我发现这里也没处理最后一个Uhou还是V的情况，草问题也太多了吧啊啊啊啊啊啊！
                if Uqian[flag].k == None:  # !!!!!这其实是很要紧的一种情况，因为整个U开始之前就会走到这来，U开始前怎么存？
                    k = k
                    if flag == 0:
                        Uqian_this = Uqian[0:flag + 1]
                    else:
                        Uqian_this = Uqian[0:flag]
                else:
                    k = U_st_list[flag] + Uqian[flag].k + 1  # 这里和上边不一样了，在这里就加1，懒得再搞了
                    Uqian_this = Uqian[0:flag + 1]
                for i in range(len(Uhou_list_k_original[flag])):
                    if jicheng != None:
                        is_cuowei = self.is_cuowei(jicheng, Uhou_list_k_original[flag][i])
                        if not is_cuowei:
                            continue
                    if Uhou_list_k_original[flag][i].sat == "violated":  # 这个最上边已经处理过了
                        continue
                    if Uhou_list_k_original[flag][i].k == None and flag != 0:  # 当这个不是第一个且还没开始时就不存了
                        linshi_list_this = linshi_list
                    else:
                        linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                    if Uhou_list_k_original[flag][i].k == None:  # 这个Uhou还没开始，俩都不确定
                        p = Probability(False, U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k)
                        result += [p]
                    else:
                        p = Probability(False, U_st_list[flag], 'U', U_st_list, [Uqian_this, linshi_list_this], k)
                        result += [p]
        return result

    def pailiezuhe_U(self, Uqian, Uhou_list_k_original, U_st_list, num, linshi_list=[], flag=0):
        #  如果Uqian.k > max(Uhou.k)，那后边肯定是全排列
        # 这个还没写完呢，搁置一下，不知道怎么写了
        result = []
        if flag < (num - 1):
            if Uqian.sat == "violated":
                if U_st_list[flag] < Uqian.start_time:
                    for i in range(len(Uhou_list_k_original[flag])):
                        if Uhou_list_k_original[flag][i].sat == True:
                            linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                            k = max()
                            p = Probability(True, U_st_list[flag],'U', U_st_list,[Uqian, linshi_list_this], max())
                            p.self_check_U(U_st_list)
                            result += [p]

                    for i in range(len(Uhou_list_k_original[flag])):
                        if Uhou_list_k_original[flag][i].sat != "violated":
                            linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                            result += self.pailiezuhe_U(Uqian, Uhou_list_k_original, num, linshi_list_this, flag + 1)
                        else:
                            linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                            result += [linshi_list_this]
        else:
            for i in range(len(Uhou_list_k_original[flag])):
                linshi_list_this = linshi_list + [Uhou_list_k_original[flag][i]]
                result += [linshi_list_this]
        return result

    def is_cuowei(self, P, P_next):
        # 我要在这写一个能判断进来的是P还是P_Phi的，然后之后把下边那个is_cuowei的名字改了，如果进来的是P就调用下边那个，否则用这个，
        # 这样不影响之前用之前那个is_cuowei的地方，相当于扩展下边那个的功能让他能判断P_Phi了
        is_cuowei = True  # 先默认满足
        if type(P) == type(Probability()) or P.P_list == None:
            is_cuowei = self.is_cuowei_P(P, P_next)
        elif type(P) == type(Probability_Phi()):
            for i in range(len(P.P_list)):
                if not self.is_cuowei_P(P.P_list[i], P_next.P_list[i]):
                    is_cuowei = False
                    break
        return is_cuowei

    def is_cuowei_P(self, P, P_next):
        #  判断两个P是否满足连续关系，但P_Phi不能传进来，因为P_Phi的P_list里并不是时间连续关系，而是∧并列关系
        #  !但是，[]类型的P_Phi可以传进来，因为肯定可以后继，而且P_list为None，一定return True，这样就实现了最底层[]和上层的统一
        #  因为上层也不是直接处理P_Phi的，而是每个子公式即每个P分开处理的
        is_cuowei = True  # 先默认满足
        if P.P_list != None:  # 如果是None说明没开始？没开始就肯定是后继了，因为我的P_list里没东西怎么可能跟你矛盾呢？
            if P.operator == 'G':
                for j in range(len(P.P_list) - 1):  # 取前后连续的P_list的交叉部分，分别看是不是相等，后一个的st处对应等于前一个st+1处
                    if not P_next.P_list[j].is_equal(P.P_list[j + 1]):  # 只要出现不相等则不满足后继条件，is_cuowei=False，然后break掉
                        is_cuowei = False
                        break
            elif P.operator == 'U':
                # print(P.P_list)
                # print(P_next.P_list)
                # print()
                if len(P_next.P_list[0]) < len(P.P_list[0]) - 1 or len(P_next.P_list[1]) < len(P.P_list[1]) - 1:
                    is_cuowei = False
                    return is_cuowei
                for j in range(len(P.P_list[0]) - 1):  # 取前后连续的P_list的交叉部分，分别看是不是相等，后一个的st处对应等于前一个st+1处
                    if not P_next.P_list[0][j].is_equal(P.P_list[0][j + 1]):  # 只要出现不相等则不满足后继条件，is_cuowei=False，然后break掉
                        is_cuowei = False
                        return is_cuowei
                for j in range(len(P.P_list[1]) - 1):  # 取前后连续的P_list的交叉部分，分别看是不是相等，后一个的st处对应等于前一个st+1处
                    if not P_next.P_list[1][j].is_equal(P.P_list[1][j + 1]):  # 只要出现不相等则不满足后继条件，is_cuowei=False，然后break掉
                        is_cuowei = False
                        return is_cuowei
        return is_cuowei

    def pailiezuhe_lianxv(self, original_list_k, num, linshi_list=[], jicheng=None, flag=0):
        #  [a,a+1,...,b]
        #  输入 : [[a开始的在k时刻可能的所有情况P_Phi],[a+1开始的在k时刻可能的所有情况P_Phi],...,[[b开始的在k时刻可能的所有情况P_Phi]]]
        #  输出 : [[a开始的到b开始的的每个的某种可能情况P_Phi],[a开始的到b开始的的每个的某种可能情况P_Phi],...]
        #  处理的元素是P_Phi，前后之间要满足错位条件
        #  如果第一个是None就存(说明第一个就没开始)，否则就不存None了(说明已经有开始的了)
        result = []
        if flag < (num-1):
            for i in range(len(original_list_k[flag])):
                if original_list_k[flag][i].k == None:
                    if flag == 0:  # 第一个都没开始的时候存None，第一个开始之后就不再存None了
                        linshi_list_this = linshi_list + [original_list_k[flag][i]]
                        result += [linshi_list_this]
                    else:
                        linshi_list_this = linshi_list
                        result += [linshi_list_this]
                    continue
                if jicheng != None:
                    is_cuowei = self.is_cuowei(jicheng, original_list_k[flag][i])
                    if not is_cuowei:
                        continue
                linshi_list_this = linshi_list + [original_list_k[flag][i]]
                result += self.pailiezuhe_lianxv(original_list_k, num, linshi_list_this, original_list_k[flag][i], flag+1)
        else:
            for i in range(len(original_list_k[flag])):
                if original_list_k[flag][i].k == None:
                    if flag == 0:  # 第一个都没开始的时候存None，第一个开始之后就不再存None了
                        linshi_list_this = linshi_list + [original_list_k[flag][i]]
                        result += [linshi_list_this]
                    else:
                        linshi_list_this = linshi_list
                        result += [linshi_list_this]
                    continue
                if jicheng != None:
                    is_cuowei = self.is_cuowei(jicheng, original_list_k[flag][i])
                    if not is_cuowei:
                        continue
                linshi_list_this = linshi_list + [original_list_k[flag][i]]
                result += [linshi_list_this]
        return result

    #  用于生成该Phi在一定已经结束(无论是T或者V)之前每一个k时所有可能的情况(包括T,F,V)
    def heihe_v(self):
        all_horizon = []
        all_list = []
        for i in range(0, len(self.a)):
            linshi_horizon = []
            linshi_list = []
            if len(self.a) == 1:
                effctive = self.effective_horizon()
            else:  # 记下第i个子公式的有效时间
                effctive = self.Phi_list[i].effective_horizon()
            if self.operator[i] == 'G':
                if type(self.phi[i]) == type([]):
                    G_st_list = list(range(self.a[i], self.b[i] + 1))
                    for k in range(-1,effctive[1] + 2):
                        linshi_list_k = []
                        G_list_k_original = []
                        for st in range(self.a[i],self.b[i]+1):
                            if k - st > 0:  # 对于[]来说已经开始的只能是T或V
                                G_list_k_original += [[Probability_Phi(True, 0, None, self.phi[i]), Probability_Phi("violated", 0, None, self.phi[i])]]
                            elif k-st==0:  # 刚开始也为F，但k置为-1
                                G_list_k_original += [[Probability_Phi(False, -1, None, self.phi[i])]]
                            else:  # 而没开始的只能是F，k为None
                                G_list_k_original += [[Probability_Phi(False, None, None, self.phi[i])]]
                        # [a,a+1,...,b]
                        # [[k时a开始的P_Phi的各种可能],[k时a+1开始的P_Phi的各种可能],...,[k时b开始的P_Phi的各种可能]]
                        # print(f"G{k}")
                        # print(f"排列前:{G_list_k_original}")
                        G_list_k = self.pailiezuhe_G(G_list_k_original, len(G_list_k_original))
                        # print(f"排列后:{G_list_k}")
                        for n in range(len(G_list_k)):
                            if k == -1:
                                p = Probability(None, None, 'G', G_st_list, G_list_k[n], None)
                            else:
                                p = Probability(None, None, 'G', G_st_list, G_list_k[n], k)
                            # p.self_check_G()
                            linshi_list_k += [p]
                        linshi_list += [linshi_list_k]
                    linshi_list += [linshi_list.pop(0)]
                    all_horizon += [list(range(effctive[1] + 1))]
                    all_list += [linshi_list]  # 后边要设如果没在范围里，出去了是T(b),V(a),V(a+1)...V(b)

                elif type(self.phi[i]) == type(self):
                    heihe_v_horizon, heihe_v_list, p_phi_list = self.phi[i].heihe_v()
                    operator_list = []
                    for i1 in range(len(self.phi[i].a)):
                        operator_list += [self.phi[i].operator[i1]]
                    G_st_list = list(range(self.a[i], self.b[i] + 1))
                    heihe_effctive_horizon = list(range(0, self.phi[i].effective_horizon()[1]+2))
                    for k in range(-1, effctive[1]+2):  # 必为T前每个时刻可能有的情况(即使只有一个情况也要记录)
                        linshi_list_k = []
                        G_list_k = []
                        G_list_k_original = []
                        for st in range(self.a[i], self.b[i]+1):  # 每个内层子公式的开始时间  !!!这个地方应该后边可以改成min(k,self.b[i])+1
                            # print(k-st)
                            if k - st < 0:  # 该st还没start，必为F(a),和heihe_v_list[i1][0]应该是一样的
                                #  现在不该一样了，没start的时候k取None，start了之后k取0才对，需要再在黑盒的输出里多存一个未开始情况
                                G_list_k_original += [p_phi_list[-1]]  # 还没开始，取heihe里索引为-1的
                            elif (k - st) in heihe_effctive_horizon:  # 对于该st开始的第i1个内层子公式，k时刻其可能有的情况
                                G_list_k_original += [p_phi_list[k-st]]  # 存下其当前时刻可能的[“情况”(们)]
                            else:  # 已经出去了,取heihe里索引为-2
                                G_list_k_original += [p_phi_list[-2]]
                        #  现在linshi_v_list_k_every里的存法是i1运算符子公式在k时刻的 每一个st开始的 在此时的所有可能情况
                        #  [a,a+1,...,b]
                        #  [[a开始的那个i1在k时刻可能的所有情况P],[a+1开始的那个i1在k时刻可能的所有情况P],...,[[b开始的那个i1在k时刻可能的所有情况P]]]
                        #  我们希望其变成
                        #  [[a开始的到b开始的的每个的某种可能情况P],[a开始的到b开始的的每个的某种可能情况P],...]
                        #  这些情况并不是上边的任意排列组合，需要有某些约束，所以用pailiezuhe_lianxv而非pailiezuhe
                        # print(k)
                        G_list_k = self.pailiezuhe_lianxv(G_list_k_original, len(G_list_k_original))
                        print(f"G{k}")
                        print(G_list_k)

                        for n in range(len(G_list_k)):
                            p = Probability(None, None, 'G', G_st_list, G_list_k[n], k)
                            if k == -1:
                                p.k = None
                                linshi_list_k += [p]
                                continue
                            # already_have = False
                            # for j in range(len(linshi_list_k)):
                            #     if p.is_equal(linshi_list_k[j]):
                            #         already_have = True
                            # if not already_have:
                            #     linshi_list_k += [p]
                            else:
                                if p.k == k-1:
                                    linshi_list_k += [p]
                        if linshi_list != []:
                            for p_yiqian in linshi_list[-1]:
                                if p_yiqian.sat != False:
                                    linshi_list_k += [p_yiqian]
                        print(linshi_list_k)

                        linshi_list += [linshi_list_k]

                    linshi_list += [linshi_list.pop(0)]
                    all_horizon += [list(range(effctive[1] + 1))]
                    all_list += [linshi_list]


            elif self.operator[i] == 'U':
                if type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type([]):
                    U_st_list = list(range(self.a[i], self.b[i] + 1))
                    for k in range(-1, effctive[1] + 2):
                        # 先把Uhou搞出来
                        linshi_list_k = []
                        Uhou_list_k_original = []
                        for st in range(self.a[i],self.b[i]+1):
                            if k - st > 0:  # 对于[]来说已经开始的只能是T或V
                                Uhou_list_k_original += [[Probability_Phi(True, 0, None, self.phi[i]), Probability_Phi("violated", 0, None, self.phi[i])]]
                            elif k - st == 0:  # 刚开始也为F，但k置为-1
                                Uhou_list_k_original += [[Probability_Phi(False, -1, None, self.phi[i])]]
                            else:  # 而没开始的只能是F，k为None
                                Uhou_list_k_original += [[Probability_Phi(False, None, None, self.phi[i])]]
                        # 再把Uqian搞出来
                        Uqian_list_k_original = []
                        for st in range(self.a[i], self.b[i] + 1):
                            if k - st > 0:  # 对于[]来说已经开始的只能是T或V
                                Uqian_list_k_original += [[Probability_Phi(True, 0, None, self.phi_1[i]), Probability_Phi("violated", 0, None, self.phi_1[i])]]
                            elif k - st == 0:  # 刚开始也为F，但k置为-1
                                Uqian_list_k_original += [[Probability_Phi(False, -1, None, self.phi_1[i])]]
                            else:  # 而没开始的只能是F，k为None
                                Uqian_list_k_original += [[Probability_Phi(False, None, None, self.phi_1[i])]]
                        # print(Uqian_list_k_original)
                        Uqian_list_k = self.pailiezuhe_G(Uqian_list_k_original, len(Uqian_list_k_original))
                        # print(f"U{k}")
                        # print(f"排好的各个Uqian: {Uqian_list_k}")
                        # print(f"还没排的Uhou:    {Uhou_list_k_original}")

                        U_list_k = []

                        Uhou_list_k = self.pailiezuhe(Uhou_list_k_original, len(Uhou_list_k_original))
                        for Uqian in Uqian_list_k:
                            U_list_k += self.pailiezuhe_U1(Uqian, Uhou_list_k_original, U_st_list, len(Uhou_list_k_original), k)
                        # print(U_list_k)

                        for n in range(len(U_list_k)):
                            if k == -1:  # 给没开始的安排一个k=None的
                                p = U_list_k[n]
                                p.k = None
                                linshi_list_k += [p]
                                continue
                            p = U_list_k[n]
                            already_have = False
                            for j in range(len(linshi_list_k)):
                                if p.is_equal(linshi_list_k[j]):
                                    already_have = True
                            if not already_have:
                                linshi_list_k += [p]
                        # print(f"理论上这里应该只有k={k - 1}的:{linshi_list_k}")

                        #  把那些之前完成的也加进来
                        over_in_the_past = []
                        if linshi_list != []:
                            for p_past in linshi_list[-1]:
                                if p_past.sat != False:
                                    over_in_the_past += [p_past]
                        linshi_list_k += over_in_the_past
                        # print(f"全部的:{linshi_list_k}")
                        # print(linshi_list_k)

                        linshi_list += [linshi_list_k]

                    linshi_list += [linshi_list.pop(0)]
                    all_horizon += [list(range(self.b[i] + 1))]
                    all_list += [linshi_list]  # 后边要设如果没在范围里，出去了是T或V(a),V(a+1)...V(b)

                elif type(self.phi_1[i]) == type([]) and type(self.phi[i]) == type(self):
                    #  先算U后边的各种情况，每个情况最后折成一个T/F(st)
                    heihe_v_horizon, heihe_v_list, p_phi_list = self.phi[i].heihe_v()
                    heihe_effctive_horizon = list(range(0, self.phi[i].effective_horizon()[1] + 2))
                    U_st_list = list(range(self.a[i], self.b[i] + 1))
                    Uhou_operator_list = []
                    for i1 in range(len(self.phi[i].a)):
                        Uhou_operator_list += [self.phi[i].operator[i1]]
                    for k in range(-1, effctive[1] + 2):  # 必为T前每个时刻可能有的情况(即使只有一个情况也要记录)
                        linshi_list_k = []
                        # 先把Uqian搞出来
                        Uqian_list_k_original = []
                        for st in range(self.a[i], self.b[i] + 1):
                            if k - st > 0:  # 对于[]来说已经开始的只能是T或V
                                Uqian_list_k_original += [[Probability_Phi(True, 0, None, self.phi_1[i]), Probability_Phi("violated", 0, None, self.phi_1[i])]]
                            elif k - st == 0:  # 刚开始也为F，但k置为-1
                                Uqian_list_k_original += [[Probability_Phi(False, -1, None, self.phi_1[i])]]
                            else:  # 而没开始的只能是F，k为None
                                Uqian_list_k_original += [[Probability_Phi(False, None, None, self.phi_1[i])]]
                        # print(Uqian_list_k_original)
                        Uqian_list_k = self.pailiezuhe_G(Uqian_list_k_original, len(Uqian_list_k_original))

                        # 再搞Uhou
                        Uhou_list_k = []
                        Uhou_list_k_original = []
                        for st in range(self.a[i],
                                        self.b[i] + 1):  # 每个内层子公式的开始时间  !!!这个地方应该后边可以改成min(k,self.b[i])+1
                            # print(k-st)
                            if k - st < 0:  # 该st还没start，必为F(a),和heihe_v_list[i1][0]应该是一样的
                                #  现在不该一样了，没start的时候k取None，start了之后k取0才对，需要再在黑盒的输出里多存一个未开始情况
                                Uhou_list_k_original += [p_phi_list[-1]]  # 还没开始，取heihe里索引为-1的
                            elif (k - st) in heihe_effctive_horizon:  # 对于该st开始的第i1个内层子公式，k时刻其可能有的情况
                                Uhou_list_k_original += [p_phi_list[k - st]]  # 存下其当前时刻可能的[“情况”(们)]
                            else:  # 已经出去了,取heihe里索引为-2
                                Uhou_list_k_original += [p_phi_list[-2]]
                        #  现在linshi_v_list_k_every里的存法是i1运算符子公式在k时刻的 每一个st开始的 在此时的所有可能情况
                        #  [a,a+1,...,b]
                        #  [[a开始的那个i1在k时刻可能的所有情况P],[a+1开始的那个i1在k时刻可能的所有情况P],...,[[b开始的那个i1在k时刻可能的所有情况P]]]
                        #  我们希望其变成
                        #  [[a开始的到b开始的的每个的某种可能情况P],[a开始的到b开始的的每个的某种可能情况P],...]
                        #  这些情况并不是上边的任意排列组合，需要有某些约束，所以用pailiezuhe_lianxv而非pailiezuhe
                        # print(k)
                        Uhou_list_k = self.pailiezuhe_lianxv(Uhou_list_k_original, len(Uhou_list_k_original))

                        # print(f"U{k}")
                        # print(f"排好的各个Uqian: {Uqian_list_k}")
                        # # print(f"没排的的Uhou: {Uhou_list_k_every_original}")
                        # print(f"排好了的Uhou: {Uhou_list_k}")

                        # 下边是我做的一个小小尝试，出于我对我写的self_check_U的无敌信任，那么让我们来看看它是否承受的起这份信任吧！
                        for Uqian in Uqian_list_k:
                            for Uhou in Uhou_list_k:
                                p = Probability(None, None, 'U', U_st_list, [Uqian, Uhou], k)
                                if k == -1:  # 给没开始的安排一个k=None的
                                    p.k = None
                                    linshi_list_k += [p]
                                    continue
                                if p.k == k-1:
                                    linshi_list_k += [p]
                        # print(linshi_list_k)
                        #  把那些之前完成的也加进来
                        over_in_the_past = []
                        if linshi_list != []:
                            for p_past in linshi_list[-1]:
                                if p_past.sat != False:
                                    over_in_the_past += [p_past]
                        linshi_list_k += over_in_the_past
                        # print(f"全部的:{linshi_list_k}")

                        linshi_list += [linshi_list_k]

                    linshi_list += [linshi_list.pop(0)]

                    all_horizon += [list(range(effctive[1] + 1))]
                    all_list += [linshi_list]

                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type([]):
                    Uqian_heihe_v_horizon, Uqian_heihe_v_list, Uqian_p_phi_list = self.phi_1[i].heihe_v()
                    Uqian_effctive_horizon = list(range(0, self.phi_1[i].effective_horizon()[1] + 2))
                    Uqian_operator_list = []
                    for i1 in range(len(self.phi_1[i].a)):
                        Uqian_operator_list += [self.phi_1[i].operator[i1]]
                    U_st_list = list(range(self.a[i], self.b[i] + 1))
                    for k in range(-1, effctive[1] + 2):  # 从没开始(存在[-1])到必已结束的第一个时刻(存在[-2])每个时刻可能有的情况
                        linshi_list_k = []
                        # 先把Uhou搞出来
                        Uhou_list_k_original = []
                        for st in range(self.a[i], self.b[i] + 1):
                            if k - st > 0:  # 对于[]来说已经开始的只能是T或V
                                Uhou_list_k_original += [[Probability_Phi(True, 0, None, self.phi[i]), Probability_Phi("violated", 0, None, self.phi[i])]]
                            elif k - st == 0:  # 刚开始也为F，但k置为-1
                                Uhou_list_k_original += [[Probability_Phi(False, -1, None, self.phi[i])]]
                            else:  # 而没开始的只能是F，k为None
                                Uhou_list_k_original += [[Probability_Phi(False, None, None, self.phi[i])]]
                        Uhou_list_k = self.pailiezuhe_lianxv(Uhou_list_k_original,len(Uhou_list_k_original))
                        #  再处理Uqian
                        Uqian_list_k = []
                        Uqian_list_k_original = []
                        for st in range(self.a[i],
                                        self.b[i] + 1):  # 每个内层子公式的开始时间  !!!这个地方应该后边可以改成min(k,self.b[i])+1
                            # print(k-st)
                            if k - st < 0:  # 该st还没start，必为F(a),和heihe_v_list[i1][0]应该是一样的
                                #  现在不该一样了，没start的时候k取None，start了之后k取0才对，需要再在黑盒的输出里多存一个未开始情况
                                Uqian_list_k_original += [Uqian_p_phi_list[-1]]  # 还没开始，取heihe里索引为-1的
                            elif (k - st) in Uqian_effctive_horizon:  # 对于该st开始的第i1个内层子公式，k时刻其可能有的情况
                                Uqian_list_k_original += [Uqian_p_phi_list[k - st]]  # 存下其当前时刻可能的[“情况”(们)]
                            else:  # 已经出去了,取heihe里索引为-2
                                Uqian_list_k_original += [Uqian_p_phi_list[-2]]
                        #  现在linshi_v_list_k_every里的存法是i1运算符子公式在k时刻的 每一个st开始的 在此时的所有可能情况
                        #  [a,a+1,...,b]
                        #  [[a开始的那个i1在k时刻可能的所有情况P],[a+1开始的那个i1在k时刻可能的所有情况P],...,[[b开始的那个i1在k时刻可能的所有情况P]]]
                        #  我们希望其变成
                        #  [[a开始的到b开始的的每个的某种可能情况P],[a开始的到b开始的的每个的某种可能情况P],...]
                        #  这些情况并不是上边的任意排列组合，需要有某些约束，所以用pailiezuhe_lianxv而非pailiezuhe
                        print(k)
                        Uqian_list_k = self.pailiezuhe_lianxv(Uqian_list_k_original, len(Uqian_list_k_original))

                        # 下边是我做的一个小小尝试，出于我对我写的self_check_U的无敌信任，那么让我们来看看它是否承受的起这份信任吧！
                        for Uqian in Uqian_list_k:
                            for Uhou in Uhou_list_k:
                                p = Probability(None, None, 'U', U_st_list, [Uqian, Uhou], k)
                                if k == -1:  # 给没开始的安排一个k=None的
                                    p.k = None
                                    linshi_list_k += [p]
                                    continue
                                if p.k == k - 1:
                                    linshi_list_k += [p]
                        print(linshi_list_k)
                        #  把那些之前完成的也加进来
                        over_in_the_past = []
                        if linshi_list != []:
                            for p_past in linshi_list[-1]:
                                if p_past.sat != False:
                                    over_in_the_past += [p_past]
                        linshi_list_k += over_in_the_past
                        print(f"全部的:{linshi_list_k}")

                        linshi_list += [linshi_list_k]

                    linshi_list += [linshi_list.pop(0)]
                    all_horizon += [list(range(effctive[1] + 1))]
                    all_list += [linshi_list]

                elif type(self.phi_1[i]) == type(self) and type(self.phi[i]) == type(self):
                    #  先算U两边的各种情况，每个情况最后折成一个T/F(st)
                    Uqian_v_horizon, Uqian_v_list, Uqian_p_phi_list = self.phi_1[i].heihe_v()
                    Uqian_effctive_horizon = list(range(0, self.phi_1[i].effective_horizon()[1] + 2))
                    Uhou_v_horizon, Uhou_v_list, Uhou_p_phi_list = self.phi[i].heihe_v()
                    Uhou_effctive_horizon = list(range(0, self.phi[i].effective_horizon()[1] + 2))
                    U_st_list = list(range(self.a[i], self.b[i] + 1))
                    for k in range(-1, effctive[1] + 2):  # 必为T前每个时刻可能有的情况(即使只有一个情况也要记录)
                        linshi_list_k = []

                        # 先把Uqian搞出来
                        Uqian_list_k = []
                        Uqian_list_k_original = []
                        for st in range(self.a[i],
                                        self.b[i] + 1):  # 每个内层子公式的开始时间  !!!这个地方应该后边可以改成min(k,self.b[i])+1
                            # print(k-st)
                            if k - st < 0:  # 该st还没start，必为F(a),和heihe_v_list[i1][0]应该是一样的
                                #  现在不该一样了，没start的时候k取None，start了之后k取0才对，需要再在黑盒的输出里多存一个未开始情况
                                Uqian_list_k_original += [Uqian_p_phi_list[-1]]  # 还没开始，取heihe里索引为-1的
                            elif (k - st) in Uqian_effctive_horizon:  # 对于该st开始的第i1个内层子公式，k时刻其可能有的情况
                                Uqian_list_k_original += [Uqian_p_phi_list[k - st]]  # 存下其当前时刻可能的[“情况”(们)]
                            else:  # 已经出去了,取heihe里索引为-2
                                Uqian_list_k_original += [Uqian_p_phi_list[-2]]
                        #  现在linshi_v_list_k_every里的存法是i1运算符子公式在k时刻的 每一个st开始的 在此时的所有可能情况
                        #  [a,a+1,...,b]
                        #  [[a开始的那个i1在k时刻可能的所有情况P],[a+1开始的那个i1在k时刻可能的所有情况P],...,[[b开始的那个i1在k时刻可能的所有情况P]]]
                        #  我们希望其变成
                        #  [[a开始的到b开始的的每个的某种可能情况P],[a开始的到b开始的的每个的某种可能情况P],...]
                        #  这些情况并不是上边的任意排列组合，需要有某些约束，所以用pailiezuhe_lianxv而非pailiezuhe
                        Uqian_list_k = self.pailiezuhe_lianxv(Uqian_list_k_original, len(Uqian_list_k_original))

                        # 再搞Uhou
                        Uhou_list_k = []
                        Uhou_list_k_original = []
                        for st in range(self.a[i],
                                        self.b[i] + 1):  # 每个内层子公式的开始时间  !!!这个地方应该后边可以改成min(k,self.b[i])+1
                            # print(k-st)
                            if k - st < 0:  # 该st还没start，必为F(a),和heihe_v_list[i1][0]应该是一样的
                                #  现在不该一样了，没start的时候k取None，start了之后k取0才对，需要再在黑盒的输出里多存一个未开始情况
                                Uhou_list_k_original += [Uhou_p_phi_list[-1]]  # 还没开始，取heihe里索引为-1的
                            elif (k - st) in Uhou_effctive_horizon:  # 对于该st开始的第i1个内层子公式，k时刻其可能有的情况
                                Uhou_list_k_original += [Uhou_p_phi_list[k - st]]  # 存下其当前时刻可能的[“情况”(们)]
                            else:  # 已经出去了,取heihe里索引为-2
                                Uhou_list_k_original += [Uhou_p_phi_list[-2]]
                        #  现在linshi_v_list_k_every里的存法是i1运算符子公式在k时刻的 每一个st开始的 在此时的所有可能情况
                        #  [a,a+1,...,b]
                        #  [[a开始的那个i1在k时刻可能的所有情况P],[a+1开始的那个i1在k时刻可能的所有情况P],...,[[b开始的那个i1在k时刻可能的所有情况P]]]
                        #  我们希望其变成
                        #  [[a开始的到b开始的的每个的某种可能情况P],[a开始的到b开始的的每个的某种可能情况P],...]
                        #  这些情况并不是上边的任意排列组合，需要有某些约束，所以用pailiezuhe_lianxv而非pailiezuhe
                        # print(k)
                        Uhou_list_k = self.pailiezuhe_lianxv(Uhou_list_k_original, len(Uhou_list_k_original))

                        print(f"U{k}")
                        print(f"排好的各个Uqian: {Uqian_list_k}")
                        print(f"排好了的Uhou: {Uhou_list_k}")

                        # 下边是我做的一个小小尝试，出于我对我写的self_check_U的无敌信任，那么让我们来看看它是否承受的起这份信任吧！
                        for Uqian in Uqian_list_k:
                            for Uhou in Uhou_list_k:
                                p = Probability(None, None, 'U', U_st_list, [Uqian, Uhou], k)
                                if k == -1:  # 给没开始的安排一个k=None的
                                    # p = U_list_k[n]
                                    p.k = None
                                    linshi_list_k += [p]
                                    continue
                                if p.k == k - 1:
                                    # already_have = False
                                    # for j in range(len(linshi_list_k)):
                                    #     if p.is_equal(linshi_list_k[j]):
                                    #         already_have = True
                                    #         break
                                    # if not already_have:
                                    #     linshi_list_k += [p]
                                    #  已检验过把下边这个换成上边那个检测重复的之后结果没有任何区别，说明现在的这里边确实是没有重复的情况
                                    #  且都能保证是当前这一刻发生的，不会出现之前时刻已经结束了而后边还在排列组合导致多情况的情况发生
                                    linshi_list_k += [p]
                        print(linshi_list_k)
                        #  把那些之前完成的也加进来
                        over_in_the_past = []
                        if linshi_list != []:
                            for p_past in linshi_list[-1]:
                                if p_past.sat != False:
                                    over_in_the_past += [p_past]
                        linshi_list_k += over_in_the_past
                        print(f"全部的:{linshi_list_k}")

                        linshi_list += [linshi_list_k]

                    linshi_list += [linshi_list.pop(0)]
                    all_horizon += [list(range(effctive[1] + 1))]
                    all_list += [linshi_list]

        # 在这里把每个子公式并列的分别的P，处理成每个k时刻整个的P_Phi，以防止某个V了别的后边还在继续进行的情况在之后又被排列组合出来
        p_phi_list = []
        for k in range(-1, self.effective_horizon()[1] + 2):
            p_phi_list_k = []
            if k == -1:  # 都还没开始呢
                linshi_list = []
                for i in range(len(self.a)):
                    linshi_list += [all_list[i][-1][0]]
                # print(linshi_list)
                p_phi = Probability_Phi(None, None, linshi_list)
                p_phi_list_k += [p_phi]
                p_phi_list += [p_phi_list_k]
            else:
                linshi_list_original = []
                for i in range(len(self.a)):
                    if k in all_horizon[i]:
                        linshi_list_original += [all_list[i][k]]
                    else: # 这个子公式i已经结束了，取-2
                        linshi_list_original += [all_list[i][-2]]
                # print("-------------------------------------------------------------------------------")
                # print(f"k:{k}")
                # print(linshi_list_original)
                linshi_list = self.pailiezuhe(linshi_list_original, len(linshi_list_original))
                # print(len(linshi_list))
                # print(linshi_list)
                for n in range(len(linshi_list)):
                    p_phi = Probability_Phi(None, None, linshi_list[n])
                    if p_phi.k == k-1:
                        p_phi_list_k += [p_phi]
                # print(len(p_phi_list_k))
                # print(p_phi_list_k)
                # 然后再把以前完成的加进来
                for p_phi_yiqian in p_phi_list[-1]:
                    if p_phi_yiqian.sat != False:
                        p_phi_list_k += [p_phi_yiqian]
                # print(p_phi_list_k)
                p_phi_list += [p_phi_list_k]

        p_phi_list += [p_phi_list.pop(0)]

        return all_horizon, all_list, p_phi_list

    def potential_set(self):
        heihe_v_horizon, heihe_v_list, p_phi_list = self.heihe_v()
        p_list = []
        for k in range(0, self.effective_horizon()[1] + 2):  # 必为T前每个时刻可能有的情况(即使只有一个情况也要记录)
            p_list_k = []
            p_list_k_every_original = []
            for i1 in range(len(heihe_v_horizon)):  # 遍历每个内层子公式
                if k in heihe_v_horizon[i1]:  # 对于该st开始的第i1个内层子公式，k时刻其可能有的情况
                    p_list_k_every_original += [heihe_v_list[i1][k]]  # 存下其当前时刻可能的[“情况”(们)]
                else:  # 已经出去了,取heihe里索引为-2
                    p_list_k_every_original += [heihe_v_list[i1][-2]]
            p_list_k = self.pailiezuhe_not_v(p_list_k_every_original, len(p_list_k_every_original))
            p_list += [p_list_k]
        return p_list

    def is_successor(self, p_list_k, p_list_next_k):
        # 用来检测一个k+1时刻的索引集I'是否是一个k时刻的索引集I的后继集
        is_successor= True
        for i in range(len(p_list_k)):
            # print(p_list_k[i].P_list)
            # print(p_list_next_k[i].P_list)
            if p_list_k[i].sat == True or p_list_k[i].sat == "violated":  # 已经T了的下一个也得T，而且应该是一样的T
                if not p_list_next_k[i].is_equal(p_list_k[i]):
                    is_successor= False
                    return is_successor
            elif p_list_k[i].sat == False:
                if p_list_k[i].operator == 'G':  # 注意到p_phi.k为None时，说明这个还没开始，那下一个是啥都可以为这个的后继
                    if not len(p_list_next_k[i].P_list) >= len(p_list_k[i].P_list):
                        is_successor = False
                        return is_successor
                    for st_index in range(len(p_list_k[i].P_list)):
                        if p_list_k[i].P_list[st_index].k == None:  # 如果还没开始，k+1时这个P_Phi是啥都行，且后边的st肯定也没开始，就不用调整is_successor了且break就行
                            break
                        else:
                            if not self.is_successor_phi(p_list_k[i].P_list[st_index], p_list_next_k[i].P_list[st_index]):
                                is_successor = False
                                return is_successor
                elif p_list_k[i].operator == 'U':  # 注意到p_phi.k为None时，说明这个还没开始，那下一个是啥都可以为这个的后继
                    if not len(p_list_next_k[i].P_list[0]) >= len(p_list_k[i].P_list[0]):
                        is_successor = False
                        return is_successor
                    if not len(p_list_next_k[i].P_list[1]) >= len(p_list_k[i].P_list[1]):
                        is_successor = False
                        return is_successor
                    for st_index in range(len(p_list_k[i].P_list[0])):
                        if p_list_k[i].P_list[0][st_index].k == None:
                            break
                        else:
                            if not self.is_successor_phi(p_list_k[i].P_list[0][st_index], p_list_next_k[i].P_list[0][st_index]):
                                is_successor = False
                                return is_successor
                    for st_index in range(len(p_list_k[i].P_list[1])):
                        if p_list_k[i].P_list[1][st_index].k == None:
                            break
                        else:
                            # print(p_list_k[i].P_list[1][st_index])
                            # print(p_list_next_k[i].P_list[1][st_index])
                            if not self.is_successor_phi(p_list_k[i].P_list[1][st_index], p_list_next_k[i].P_list[1][st_index]):
                                is_successor = False
                                return is_successor
        return is_successor

    def is_successor_phi(self, p_phi_k, p_phi_next_k):
        is_successor = True
        # print(p_phi_k.P_list)
        # print(p_phi_next_k.P_list)
        if p_phi_k.P_list == None:  # 如果是[]的话，上一个信号是啥和下一个信号是啥都可以作为后继，这很显然
            # print(p_phi_k.sat)
            if p_phi_k.sat != False:  # 如果是已经T或者V的话，那下一个k的这一项得跟上一个k一眼
                if p_phi_k.sat != p_phi_next_k.sat or p_phi_k.k != p_phi_next_k.k:  #
                    is_successor = False
            return is_successor
        else:
            return self.is_successor(p_phi_k.P_list, p_phi_next_k.P_list)

    #  给两个集合取交集，考虑R以及\运算
    def jiao(self, region1, region2):
        # 用来给两个集合取交集，考虑全集R，R的存法是region = ['R'] 存了一个字符R
        if region1[0] == 'R':
            region = region2
        elif region2[0] == 'R':
            region = region1
        else: # 这种情况是两个都不是R，正常取交集即可
            if region1[0] == 'not':
                if region2[0] == 'not':
                    region = ['not', list(set(region1[1]) | set(region2[1]))]
                else:
                    region = [list(set(region2[0]) - set(region1[1]))]
            elif region2[0] == 'not':  # 这时候region1肯定不是not了
                region = [list(set(region1[0]) - set(region2[1]))]
            else:  # 俩都不是not不是R，正常取交集
                # print(region1)
                # print(region2)
                region = [list(set(region1[0]) & set(region2[0]))]
        return region

    # 从I到I'可以取的集合  H_i   对每个P单独算，再取合集作为P_Phi的consistent_region
    def consistent_region(self, p_list_k, p_list_next_k):
        # 用来计算一个k时刻的索引集I的后继集k+1时刻的索引集I'，从I到I'时x_k可取的范围
        consistent_region_every = [['R']]
        # consistent_region_every_no = []
        for i in range(len(p_list_k)):
            if p_list_k[i].sat == True or p_list_k[i].sat == "violated":  # 已经T了或V的就不需要对范围贡献了
                continue
            elif p_list_k[i].sat == False:
                if p_list_k[i].operator == 'G':  # 注意到p_phi.k为None时，说明这个还没开始，那下一个是啥都可以为这个的后继
                    for st_index in range(len(p_list_k[i].P_list)):  # 连续错位排布的只用找第一个尚未完成的即可，即为F的
                        #  上边那句话已经被辟谣了，有好几个并列的时候不能只看整体P_Phi的F，应该独立地看每个子公式的F，所以不能这么搞
                        #  还是安安生生每一个都看，最后取交集吧
                        # if p_list_k[i].P_list[st_index].sat != False:
                        #     continue
                        # print(p_list_k[i].P_list[st_index].sat)
                        if p_list_k[i].P_list[st_index].k == None:  # 如果还没开始，也不会对范围有影响，且后边肯定都没开始，直接break
                            break
                        elif p_list_k[i].P_list[st_index].sat != False:  # 或者已经结束，也不会对范围有影响
                            continue
                        else:
                            consistent_region_phi = self.consistent_region_phi(p_list_k[i].P_list[st_index], p_list_next_k[i].P_list[st_index])
                            consistent_region_every += [consistent_region_phi]
                elif p_list_k[i].operator == 'U':  # 注意到p_phi.k为None时，说明这个还没开始，那下一个是啥都可以为这个的后继
                    # print(p_list_k[i].P_list)
                    # print(p_list_next_k[i].P_list)
                    for st_index in range(len(p_list_k[i].P_list[0])):
                        if p_list_k[i].P_list[0][st_index].k == None:
                            break
                        else:
                            if p_list_k[i].P_list[0][st_index].sat != False:
                                continue
                            else:
                                consistent_region_phi = self.consistent_region_phi(p_list_k[i].P_list[0][st_index],
                                                                                   p_list_next_k[i].P_list[0][st_index])
                                consistent_region_every += [consistent_region_phi]
                    for st_index in range(len(p_list_k[i].P_list[1])):  # 这个得根据下一个k时这个Uhou是T或者V或者F来判断范围
                        if p_list_k[i].P_list[1][st_index].k == None:
                            break
                        else:
                            if p_list_k[i].P_list[1][st_index].sat != False:
                                continue
                            else:
                                consistent_region_phi = self.consistent_region_phi(p_list_k[i].P_list[1][st_index],
                                                                                   p_list_next_k[i].P_list[1][st_index])
                                consistent_region_every += [consistent_region_phi]

        # print(f"保留的:{consistent_region_every}")
        # 把所有需要满足的取交集
        consistent_region = consistent_region_every[0]
        for region in consistent_region_every:
            # consistent_region = list(set(consistent_region) & set(region))
            consistent_region = self.jiao(consistent_region, region)
        # print(f"最终的:{consistent_region}")

        return consistent_region

    def consistent_region_phi(self, p_phi_k, p_phi_next_k):
        # 传进来的p_phi_k一定是False，但p_phi_next_k不一定，需要分类讨论
        if p_phi_k.P_list == None:  # 说明已经到[]了，这时候要开始找范围了,且k处为False，k+1处一定为T或V
            consistent_region = [p_phi_k.H]
            if p_phi_next_k.sat == True:
                consistent_region = [p_phi_k.H]
            elif p_phi_next_k.sat == "violated":
                consistent_region = ['not', p_phi_k.H]
        else:
            consistent_region = self.consistent_region(p_phi_k.P_list, p_phi_next_k.P_list)
        return consistent_region

    def all_consistent_region_k(self,k):
        # 用来测试某k时到k+1时所有的I与之所有的后继集I'的consistent_region
        p = self.potential_set()
        print(f"k={k}:{p[k]}")
        print(f"k={k+1}:{p[k+1]}")
        for p_k in p[k]:
            for p_nk in p[k+1]:
                if self.is_successor(p_k, p_nk):
                    print()
                    print(p_k)
                    print(p_nk)
                    print(self.consistent_region(p_k,p_nk))

    def check_is_successor_k(self,k):
        # 用来测试某k时到k+1时所有的I与k+1时刻所有的I'两两之间是不是后继集
        p = self.potential_set()
        for p_k in p[k]:
            for p_nk in p[k+1]:
                print()
                print(p_k)
                print(p_nk)
                print(self.is_successor(p_k, p_nk))


if __name__ == "__main__":
    # #
    # # signal = [8,2,2,2,3,8,8,8]
    # o1 = Phi([1,2],[3,5],['G','U'],[[1,2],[1,3]],[None,[2,3]])
    # print(o1)
    # # print(o1.check(signal))
    #
    # o5 = Phi([1],[5],['U'],[[3,4]],[[1,2,3]])
    # # signal_5 = [1,3,3,3,1,1,1,1]
    # o8 = Phi([0],[2],['G'],[o5])
    # print(o8)
    # print(o8.effective_horizon())
    # print(o8.in_potential())
    # # print(o8.check(signal_5))
    # print(o1)
    # print(o1.effective_horizon())
    # print(o1.in_potential())
    #
    # o3 = Phi([2],[4],['G'],[[5,10,15]])
    # print(o3)
    # print(o3.effective_horizon())
    # print(o3.in_potential())
    # o7 = Phi([0],[5],['U'],[[10,100]],[o3])
    # print(o7)
    # print(o7.effective_horizon())
    # print(o7.in_potential())
    # o9 = Phi([3],[8],['G'],[[1,2]])
    # # # print(o9)
    # # # print(o9.in_potential())
    # # o10 = Phi([2],[5],['G'],[o9])
    # # print(o10)
    # # print(o10.in_potential())
    # o11 = Phi([3],[8],['U'],[[1,2]],[o9])
    # # print(o11)
    # # print(o11.in_potential())
    # o12 = Phi([3],[8],['U'],[[1,2]],[o11])
    # print(o12)
    # print(o12.in_potential())
    # print(o12.effective_horizon())
    # print(o12.I.I_list)

    # o13 = Phi([3],[8],['G'],[[1]])
    # print((o13))
    # print(o13.I)
    # print(o13.I.I_list)
    # print(o13.I.I_list[0])
    # o14 = Phi([3],[8],['G'],[o13])
    # # print((o14))
    # # print(o14.I)
    # # print(o14.I.I_list)
    # o15 = Phi([3],[8],['U'],[[1,2]],[[2,3]])
    # print(o15)
    # print(o15.I)
    # print(o15.I.I_list)
    # o16 = Phi([1],[5],['U'],[o15],[o14])
    # print(o16)
    # print(o16.I)
    # o17 = Phi([1,2],[3,5],['G','U'],[o16,[1,2]],[None,[2,3]])
    # print(o17)
    # print(o17.I)
    # o18 = Phi([3,3],[8,8],['G','U'],[[1],[1,2]],[None,[2,3]])
    # print(o18)
    # print(o18.I)
    o20 = Phi([1],[2],['G'],[[0,1]])
    # o20 = Phi([1,2],[2,3],['G','U'],[[1,2,3],[2,3]],[None,[1,2,8]])
    o21 = Phi([1],[2],['G'],[o20])
    print(o21)
    a21 = o21.heihe_v()
    print(a21[0])
    # print(a21[1])
    print(a21[2])

    print()
    print("--------------------------------------------------------------------------------------------------------------")
    print()

    o20 = Phi([1],[2],['G'],[[0,1]])
    oG2 = Phi([4],[5],['G'],[[2,3]])
    o23 = Phi([1],[2],['U'],[oG2],[o20])
    print(o23)
    a23 = o23.heihe_v()
    print(a23[0])
    print(a23[1])
    print(a23[2])

    print()
    print("--------------------------------------------------------------------------------------------------------------")
    print()

    o19 = Phi([1,2,3],[4,5,7],['G','U','U'],[[1],[2,3],[2,3]],[None,[1,2],[1,2]])
    o19 = Phi([1,2],[3,5],['G','U'],[[1,2,3],[2,3]],[None,[1,2,8]])
    # o192 = Phi([1,2,],[4,5,],['G','U'],[[1],[2,3]],[None,[1,2]])
    # o19 = Phi([1,1,6],[5,3,8],['G','U','U'],[[1],[2,3],[2,3]],[None,[1,2],[1,2]])
    print(o19)
    a19 = o19.heihe_v()
    print(a19[0])
    print(a19[1])
    print(a19[2])
    p19 = o19.potential_set()
    print(p19)
    print(o19.is_successor(p19[3][0], p19[4][1]))
    # print(o19.in_potential())
    # # # print(o19.potential_set(3)[0].I_list[0].sat)
    # print(o19.potential_set(6))
    # # print(o19.potential_set(6)[0].I_list[0].sat)
    # # print(o19.potential_set(7))
    # # print(o19.potential_set(7)[0].I_list[1].sat)
    # # print(o19.potential_set(7)[0].I_list[2].sat)
    # # print(o19.potential_set(7)[1].I_list[2].sat)
    # # print(o19.potential_set(1))
    # # print(o19.potential_set(1)[0].I_list[0].sat)
    # # print(o19.potential_set(1)[0].I_list[1].sat)
    # # print(o19.potential_set(1)[0].I_list[2].sat)
    # print(o19.potential_set(9))
    # # print(o19.potential_set(9)[0].I_list[0].sat)
    # # print(o19.potential_set(9)[0].I_list[1].sat)
    # # print(o19.potential_set(9)[0].I_list[2].sat)

    print()
    print("--------------------------------------------------------------------------------------------------------------")
    print()

    # o20 = Phi([1,6],[3,7],['U','G'],[[2,3],[0]],[[1,2],None])
    o20 = Phi([1],[2],['G'],[[0,1]])
    oG2 = Phi([4],[5],['G'],[[2,3]])
    # o20 = Phi([1],[2],['U'],[[2,3]],[[1,2]])
    print(o20)
    a20 = o20.heihe_v()
    print(a20[0])
    print(a20[1])
    print()
    o21 = Phi([1],[2],['G'],[o20])
    print(o21)
    # print(o21.I.I_list)
    a21 = o21.heihe_v()
    print(a21[0])
    print(a21[1])
    print(o21.effective_horizon())
    print(o21.in_potential())
    # print(o21.can_die_time_list())
    print()

    o22 = Phi([1],[2],['U'],[[2,3]],[o20])
    print(o22)
    a22 = o22.heihe_v()
    print(a22[0])
    print(a22[1])

    print()
    print("--------------------------------------------------------------------------------------------------------------")
    print()

    o23 = Phi([1],[2],['U'],[o20],[[2,3]])
    print(o23)
    a23 = o23.heihe_v()
    print(a23[0])
    print(a23[1])

    print()
    print("--------------------------------------------------------------------------------------------------------------")
    print()
    o24 = Phi([1],[2],['U'],[oG2],[o20])
    # o24 = Phi([1],[2],['U'],[o20],[oG2])
    # o24 = Phi([1],[2],['U'],[o19],[oG2])
    print(o24)
    print(o24.effective_horizon())
    # a24 = o24.heihe_v()
    # print(a24[0])
    # print(a24[1])
    # p24 = o24.potential_set()
    # print()
    # print(p24)

    print()
    # print(o24.is_successor(p24[6][2], p24[7][2]))
    # o24.check_is_successor_k(7)
    o24.all_consistent_region_k(6)
    print()

    # print(o20)
    # p20 = o20.potential_set()
    # print(p20)
    # print(o20.consistent_region(p20[0][0], p20[1][0]))

    # print()
    # print(o19)
    # print(p19[0])
    # print(p19[1])
    # print(p19[2])
    # print(p19[3])
    # print(p19[4])
    # print(p19[5])
    # print(p19[6])
    # # print(o19.is_successor(p19[3][0], p19[4][2]))
    # # print(o19.consistent_region(p19[3][0], p19[4][2]))
    # print(o19)
    # o19.all_consistent_region_k(3)

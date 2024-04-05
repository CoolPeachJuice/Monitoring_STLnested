import copy

from STLnested_tool import Phi
from STLnested_tool import Probability_Phi
from STLnested_tool import Probability


#  给两个列表集合取交集，考虑R以及\运算
def jiao(region1, region2):
    # 用来给两个集合取交集，考虑全集R，R的存法是region = [['R']]
    if region1[0] == 'R':
        region = region2
    elif region2[0] == 'R':
        region = region1
    else:  # 这种情况是两个都不是R，正常取交集即可
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

#  给两个列表取并集，考虑R以及\运算
def bing(region1, region2):
    # 用来给两个集合取并集，考虑全集R，R的存法是region = ['R'] 存了一个字符R
    if region1[0] == 'R':
        region = region1
    elif region2[0] == 'R':
        region = region2
    else:  # 这种情况是两个都不是R，正常取并集即可
        if region1[0] == 'not':
            if region2[0] == 'not':  # 都是not
                region = ['not', list(set(region1[1]) & set(region2[1]))]
            else:  # 1是not，2不是
                region = ['not', list(set(region1[1]) - set(region2[0]))]
        elif region2[0] == 'not':  # 这时候region1肯定不是not了
            region = [list(set(region2[1]) - set(region1[0]))]
        else:  # 俩都不是not不是R，正常取并集
            # print(region1)
            # print(region2)
            region = [list(set(region1[0]) | set(region2[0]))]
    return region

class Feasible_Set():
    # 用来存储X_k^I
    def __init__(self, k, probability_phi, X):
        self.k = k
        self.I = probability_phi
        self.X = X

    # 重写print
    def __repr__(self):
        if self.X == ['R']:
            prt = f"{self.X}"
        else:
            low = min(self.X[0])
            high = max(self.X[0])
            prt = f"[{low}, {high}]"
        # if self.X == ['R']:
        #     prt = f"{self.X}"
        # else:
        #     self.X[0].sort()
        #     prt = f"{self.X[0]}"
        return prt


def fanwei(low, high):
    # 将连续的范围转换成离散的取值列表，目前的精度为0.1
    x = round(low,1)
    list = []
    while(x <= high):
        list.append(x)
        x = x + 0.1
        x = round(x, 1)
    return list

def temperature_dynamic(x_k,u_k):
    #  建筑温度变化的数学模型
    t_s = 1
    a_e = 0.06
    a_H = 0.08
    T_h = 55  # 加热温度
    T_e = 0   # 外界环境温度
    x_k1 = x_k + t_s * (a_e*(T_e - x_k)+a_H*(T_h-x_k)*u_k)
    return x_k1

def temperature_dynamic_backward(x_k1,u_k):
    #  建筑温度变化的数学模型的逆计算
    t_s = 1
    a_e = 0.06
    a_H = 0.08
    T_h = 55  # 加热温度
    T_e = 0   # 外界环境温度
    x_k = (x_k1-t_s*a_e*T_e-t_s*a_H*T_h*u_k)/(1-t_s*a_e-t_s*a_H*u_k)
    return x_k

def one_step_set_temperature(fanwei_k):
    low_k = fanwei_k[0]
    high_k = fanwei_k[-1]
    low_k1 = temperature_dynamic(low_k, 0)
    high_k1 = temperature_dynamic(high_k, 1)
    fanwei_k1 = fanwei(low_k1,high_k1)
    return fanwei_k1

def one_step_set_temperature_backward(fanwei_k1):
    # low_k1 = fanwei_k1[0]
    # high_k1 = fanwei_k1[-1]
    low_k1 = min(fanwei_k1)
    high_k1 = max(fanwei_k1)
    low_k = temperature_dynamic_backward(low_k1, 1)
    high_k = temperature_dynamic_backward(high_k1, 0)
    # print(low_k1,high_k1)
    # print(low_k, high_k)
    fanwei_k = fanwei(low_k, high_k)
    return [fanwei_k]

def feasible_set(task):
    end = task.effective_horizon()[1]
    feasible_set_list = []
    for i in range(end+2):
        feasible_set_list += [[]]
    I_every_k = task.potential_set()
    I_every_k_phi = []
    for i in range(end+2):
        I_every_k_phi.append([])
    for i in range(end+2):
        for I_k in I_every_k[i]:
            p_phi = Probability_Phi(None, None, I_k)
            I_every_k_phi[i] += [p_phi]
            # if p_phi.sat == False:
            #     I_every_k_phi[i] += [p_phi]
    print(I_every_k_phi)
    # print(I_every_k[end+1])
    for I_T1 in I_every_k_phi[end+1]:
        # print(I_T1)
        feasible_set_list[end+1] += [Feasible_Set(end+1, I_T1, ['R'])]
    k = end
    while(k>=0):
        print(k)
        print(I_every_k_phi[k])
        for I_k in I_every_k_phi[k]:
            # 已经T了就别算了，反正是R
            if I_k.sat == True:
                continue
            # 算某个I的X_k_I，需要算其所有后继集
            X_k_I_list = []
            linshi_list = []
            for I_k1 in I_every_k_phi[k+1]:
                # print(I_k)
                # print(I_k1)
                if task.is_successor_phi(I_k, I_k1):
                    consistent_region = task.consistent_region(I_k.P_list, I_k1.P_list)
                    for X_k1 in feasible_set_list[k+1]:
                        if X_k1.I.is_equal(I_k1):
                            if X_k1.X != ['R']:
                                # print(f"here{X_k1.X}")
                                one_step_set = one_step_set_temperature_backward(X_k1.X[0])
                            else:
                                one_step_set = ['R']
                    # print(f"交:{one_step_set}和{consistent_region}")
                    # print(f"结果是:{jiao(consistent_region, one_step_set)}")
                    linshi_list += [jiao(consistent_region, one_step_set)]
            # print(f"所有后继集:{linshi_list}")
            X_k_I_list = linshi_list[0]
            for list1 in linshi_list:
                X_k_I_list = bing(X_k_I_list,list1)
            # print(X_k_I_list)
            if X_k_I_list != [[]]:
                feasible_set_list[k] += [Feasible_Set(k, I_k, X_k_I_list)]
        k = k-1
    return feasible_set_list

if __name__ == "__main__":
    # print(temperature_dynamic(20,0))
    # print(fanwei(10,15))
    # print(one_step_set_temperature(fanwei(10,15)))
    o1 = Phi([0], [5], ['G'], [fanwei(20,25)])
    # print(o1)
    # task = Phi([0,13],[5,15], ['U','G'], [o1,fanwei(27,30)], [fanwei(0,50),None])  # 在5分钟里到达[20,25]且到达后再维持5分钟
    # task = Phi([0], [5], ['U'], [o1], [fanwei(0, 50)])  # 在5分钟里到达[20,25]且到达后再维持5分钟
    task = Phi([13], [15], ['G'], [fanwei(27, 30)])  # 在5分钟里到达[20,25]且到达后再维持5分钟
    print(task)
    print(task.effective_horizon())
    I_every_k = task.potential_set()
    print(I_every_k)
    feasible_set_task = feasible_set(task)
    for i in range(16):
        print(f"k={i}")
        print(f"{len(I_every_k[i])}, {len(feasible_set_task[i])}")
        print(I_every_k[i])
        print(feasible_set_task[i])

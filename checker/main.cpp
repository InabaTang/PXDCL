#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <unordered_map>
#include <cstdlib>

using namespace std;

// 子句类型枚举
enum ClauseType {
    CNF_CLAUSE,
    XOR_CLAUSE
};

// 子句结构体
struct Clause {
    ClauseType type;
    vector<int> literals;  // 文字列表
    string original_line;  // 原始行内容
    int line_number;       // 行号
};

// 解析XN文件
vector<Clause> parseXNF(const string& filename, int& num_vars) {
    vector<Clause> clauses;
    ifstream infile(filename);
    string line;
    int num_clauses;
    
    while (getline(infile, line)) {
        if (line.empty() || line[0] == 'c') {
            continue;  // 跳过注释和空行
        }
        
        if (line[0] == 'p') {
            // 解析头部信息
            stringstream ss(line);
            string token;
            ss >> token;  // 'p'
            ss >> token;  // 'cnf'
            ss >> num_vars;
            ss >> num_clauses;
            continue;
        }
        
        // 解析子句
        Clause clause;
        clause.original_line = line;
        clause.line_number = clauses.size() + 1;
        
        stringstream ss(line);
        string first_token;
        ss >> first_token;
        
        if (first_token == "x") {
            clause.type = XOR_CLAUSE;
            // 解析异或子句
            int literal;
            while (ss >> literal && literal != 0) {
                clause.literals.push_back(literal);
            }
        } else {
            clause.type = CNF_CLAUSE;
            // 解析CNF子句
            clause.literals.push_back(stoi(first_token));
            int literal;
            while (ss >> literal && literal != 0) {
                clause.literals.push_back(literal);
            }
        }
        
        clauses.push_back(clause);
    }
    
    return clauses;
}

// 解析答案文件
unordered_map<int, bool> parseSolution(const string& filename, bool& is_satisfiable) {
    unordered_map<int, bool> assignments;
    ifstream infile(filename);
    string line;
    
    is_satisfiable = false;
    
    while (getline(infile, line)) {
        if (line.empty()) continue;
        
        stringstream ss(line);
        string token;
        ss >> token;
        
        if (token == "s") {
            string status;
            ss >> status;
            is_satisfiable = (status == "SATISFIABLE");
        } else if (token == "v") {
            int var;
            while (ss >> var && var != 0) {
                assignments[abs(var)] = (var > 0);
            }
        }
    }
    
    return assignments;
}

// 检查单个子句是否满足
bool checkClause(const Clause& clause, const unordered_map<int, bool>& assignments) {
    if (clause.type == CNF_CLAUSE) {
        // CNF子句：至少一个文字为真
        for (int literal : clause.literals) {
            int var = abs(literal);
            bool value = assignments.at(var);
            if ((literal > 0 && value) || (literal < 0 && !value)) {
                return true;  // 该文字为真
            }
        }
        return false;  // 所有文字都为假
    } else {  // XOR子句
        // 异或子句：奇数个文字为真
        int true_count = 0;
        for (int literal : clause.literals) {
            int var = abs(literal);
            bool value = assignments.at(var);
            if ((literal > 0 && value) || (literal < 0 && !value)) {
                true_count++;
            }
        }
        return (true_count % 2 == 1);  // 奇数个为真
    }
}

int main(int argc, char* argv[]) {
    if (argc != 3) {
        cout << "使用方法: " << argv[0] << " <xnf文件> <答案文件>" << endl;
        return 1;
    }
    
    string xnf_file = argv[1];
    string answer_file = argv[2];
    
    // 解析XN文件
    int num_vars;
    vector<Clause> clauses = parseXNF(xnf_file, num_vars);
    
    // 解析答案文件
    bool is_satisfiable;
    unordered_map<int, bool> assignments = parseSolution(answer_file, is_satisfiable);
    
    if (!is_satisfiable) {
        cout << "答案文件声明为不可满足" << endl;
        return 0;
    }
    
    // 检查是否所有变量都有赋值
    for (int i = 1; i <= num_vars; i++) {
        if (assignments.find(i) == assignments.end()) {
            cout << "错误: 变量 " << i << " 没有赋值" << endl;
            return 1;
        }
    }
    
    // 检查每个子句
    bool all_satisfied = true;
    for (const auto& clause : clauses) {
        if (!checkClause(clause, assignments)) {
            all_satisfied = false;
            cout << "UNSATISFIED" << endl;
            cout << "不满足的子句 (第" << clause.line_number << "行): " << clause.original_line << endl;
            
            // 输出详细信息
            cout << "子句类型: " << (clause.type == CNF_CLAUSE ? "CNF" : "XOR") << endl;
            cout << "文字: ";
            for (int literal : clause.literals) {
                cout << literal << " ";
            }
            cout << endl;
            
            // 输出每个文字的值
            cout << "各文字的值: ";
            for (int literal : clause.literals) {
                int var = abs(literal);
                bool value = assignments.at(var);
                bool literal_value = (literal > 0) ? value : !value;
                cout << literal << "=" << (literal_value ? "真" : "假") << " ";
            }
            cout << endl;
            
            if (clause.type == XOR_CLAUSE) {
                int true_count = 0;
                for (int literal : clause.literals) {
                    int var = abs(literal);
                    bool value = assignments.at(var);
                    if ((literal > 0 && value) || (literal < 0 && !value)) {
                        true_count++;
                    }
                }
                cout << "为真的文字数: " << true_count << " (需要奇数个)" << endl;
            }
            
            return 0;
        }
    }
    
    if (all_satisfied) {
        cout << "SATISFIED" << endl;
        cout << "所有子句都满足" << endl;
    }
    
    return 0;
}
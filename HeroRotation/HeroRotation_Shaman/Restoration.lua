local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 61) then
					if (Enum <= 30) then
						if (Enum <= 14) then
							if (Enum <= 6) then
								if (Enum <= 2) then
									if (Enum <= 0) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
									elseif (Enum > 1) then
										do
											return Stk[Inst[2]];
										end
									else
										local A = Inst[2];
										local T = Stk[A];
										local B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum <= 4) then
									if (Enum == 3) then
										Stk[Inst[2]] = #Stk[Inst[3]];
									else
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									end
								elseif (Enum == 5) then
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								else
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 10) then
								if (Enum <= 8) then
									if (Enum > 7) then
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local A = Inst[2];
										local C = Inst[4];
										local CB = A + 2;
										local Result = {Stk[A](Stk[A + 1], Stk[CB])};
										for Idx = 1, C do
											Stk[CB + Idx] = Result[Idx];
										end
										local R = Result[1];
										if R then
											Stk[CB] = R;
											VIP = Inst[3];
										else
											VIP = VIP + 1;
										end
									end
								elseif (Enum > 9) then
									VIP = Inst[3];
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 12) then
								if (Enum > 11) then
									Stk[Inst[2]] = {};
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								end
							elseif (Enum == 13) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 22) then
							if (Enum <= 18) then
								if (Enum <= 16) then
									if (Enum > 15) then
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
									else
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum == 17) then
									local A = Inst[2];
									Top = (A + Varargsz) - 1;
									for Idx = A, Top do
										local VA = Vararg[Idx - A];
										Stk[Idx] = VA;
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 20) then
								if (Enum == 19) then
									Stk[Inst[2]] = Inst[3];
								else
									Env[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum == 21) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 26) then
							if (Enum <= 24) then
								if (Enum > 23) then
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								else
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum > 25) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							end
						elseif (Enum <= 28) then
							if (Enum == 27) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 29) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 45) then
						if (Enum <= 37) then
							if (Enum <= 33) then
								if (Enum <= 31) then
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 32) then
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								else
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 35) then
								if (Enum == 34) then
									if (Stk[Inst[2]] < Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
								end
							elseif (Enum == 36) then
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 41) then
							if (Enum <= 39) then
								if (Enum == 38) then
									if (Stk[Inst[2]] < Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum > 40) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							else
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							end
						elseif (Enum <= 43) then
							if (Enum == 42) then
								do
									return;
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 44) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 53) then
						if (Enum <= 49) then
							if (Enum <= 47) then
								if (Enum > 46) then
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 48) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							end
						elseif (Enum <= 51) then
							if (Enum == 50) then
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum > 52) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local A = Inst[2];
							local Results = {Stk[A]()};
							local Limit = Inst[4];
							local Edx = 0;
							for Idx = A, Limit do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 57) then
						if (Enum <= 55) then
							if (Enum > 54) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							end
						elseif (Enum > 56) then
							if (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum <= 59) then
						if (Enum > 58) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 63) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum > 60) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
					end
				elseif (Enum <= 92) then
					if (Enum <= 76) then
						if (Enum <= 68) then
							if (Enum <= 64) then
								if (Enum <= 62) then
									local A = Inst[2];
									local Cls = {};
									for Idx = 1, #Lupvals do
										local List = Lupvals[Idx];
										for Idz = 0, #List do
											local Upv = List[Idz];
											local NStk = Upv[1];
											local DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
								elseif (Enum == 63) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum <= 66) then
								if (Enum == 65) then
									Stk[Inst[2]]();
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum > 67) then
								local A = Inst[2];
								local B = Inst[3];
								for Idx = A, B do
									Stk[Idx] = Vararg[Idx - A];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 72) then
							if (Enum <= 70) then
								if (Enum > 69) then
									Stk[Inst[2]] = Inst[3] ~= 0;
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum > 71) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 74) then
							if (Enum > 73) then
								local A = Inst[2];
								local Cls = {};
								for Idx = 1, #Lupvals do
									local List = Lupvals[Idx];
									for Idz = 0, #List do
										local Upv = List[Idz];
										local NStk = Upv[1];
										local DIP = Upv[2];
										if ((NStk == Stk) and (DIP >= A)) then
											Cls[DIP] = NStk[DIP];
											Upv[1] = Cls;
										end
									end
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum > 75) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						end
					elseif (Enum <= 84) then
						if (Enum <= 80) then
							if (Enum <= 78) then
								if (Enum == 77) then
									if (Stk[Inst[2]] > Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = VIP + Inst[3];
									end
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum == 79) then
								Env[Inst[3]] = Stk[Inst[2]];
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 82) then
							if (Enum == 81) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum > 83) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 88) then
						if (Enum <= 86) then
							if (Enum == 85) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum == 87) then
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 90) then
						if (Enum > 89) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						end
					elseif (Enum > 91) then
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					else
						local NewProto = Proto[Inst[3]];
						local NewUvals;
						local Indexes = {};
						NewUvals = Setmetatable({}, {__index=function(_, Key)
							local Val = Indexes[Key];
							return Val[1][Val[2]];
						end,__newindex=function(_, Key, Value)
							local Val = Indexes[Key];
							Val[1][Val[2]] = Value;
						end});
						for Idx = 1, Inst[4] do
							VIP = VIP + 1;
							local Mvm = Instr[VIP];
							if (Mvm[1] == 63) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum <= 107) then
					if (Enum <= 99) then
						if (Enum <= 95) then
							if (Enum <= 93) then
								local A = Inst[2];
								local Step = Stk[A + 2];
								local Index = Stk[A] + Step;
								Stk[A] = Index;
								if (Step > 0) then
									if (Index <= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Index >= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Enum == 94) then
								Upvalues[Inst[3]] = Stk[Inst[2]];
							else
								do
									return;
								end
							end
						elseif (Enum <= 97) then
							if (Enum == 96) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum > 98) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 103) then
						if (Enum <= 101) then
							if (Enum == 100) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum > 102) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 105) then
						if (Enum > 104) then
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Top do
								Insert(T, Stk[Idx]);
							end
						elseif (Inst[2] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 106) then
						Stk[Inst[2]] = Inst[3] ~= 0;
					elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 115) then
					if (Enum <= 111) then
						if (Enum <= 109) then
							if (Enum > 108) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum > 110) then
							local A = Inst[2];
							local B = Inst[3];
							for Idx = A, B do
								Stk[Idx] = Vararg[Idx - A];
							end
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 113) then
						if (Enum > 112) then
							Stk[Inst[2]]();
						else
							local A = Inst[2];
							Stk[A] = Stk[A]();
						end
					elseif (Enum > 114) then
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					else
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 119) then
					if (Enum <= 117) then
						if (Enum == 116) then
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 118) then
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					elseif (Stk[Inst[2]] > Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = VIP + Inst[3];
					end
				elseif (Enum <= 121) then
					if (Enum > 120) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum > 122) then
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Stk[A + 1]));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				else
					local A = Inst[2];
					local Results = {Stk[A]()};
					local Limit = Inst[4];
					local Edx = 0;
					for Idx = A, Limit do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!993Q0003073Q004865726F4442432Q033Q0044424303073Q004865726F4C696203093Q004865726F436163686503043Q00556E697403063Q00506C617965722Q033Q0050657403063Q0054617267657403053Q00466F63757303053Q005370652Q6C030A3Q004D756C74695370652Q6C03043Q004974656D03083Q004973496E5261696403123Q004765744E756D47726F75704D656D6265727303163Q00556E697447726F7570526F6C6573412Q7369676E6564030D3Q00556E697443616E412Q7461636B030C3Q004865726F526F746174696F6E03043Q004361737403113Q00436173744C6566744E616D65706C61746503053Q00416F454F4E03053Q004344734F4E03073Q00436F2Q6D6F6E7303083Q0045766572796F6E652Q033Q006E756D03043Q00622Q6F6C03073Q0047657454696D6503043Q006D6174682Q033Q006D696E03073Q00435F54696D657203053Q00416674657203143Q00476574576561706F6E456E6368616E74496E666F03063Q005368616D616E030B3Q00526573746F726174696F6E03113Q005369676E65744F665468655072696F727903023Q00494403073Q0047656E6572616C030B3Q0047554953652Q74696E67732Q033Q0041504C03093Q00436F2Q6D6F6E734453030B3Q00436F2Q6D6F6E734F474344028Q002Q033Q00416F4503103Q004865616C696E675261696E436F756E74030D3Q004865616C696E675261696E485003063Q00706C617965722Q0103063Q0070617274793103063Q0070617274793203063Q0070617274793303063Q0070617274793403093Q0053656172204D696E6403103Q0057617465727469676874205368652Q6C030E3Q0043686F6B696E672057617465727303103Q00426F6C73746572696E672053686F7574030B3Q00436F6E73756D7074696F6E03163Q0050617261736974696320506163696669636174696F6E030F3Q004861727665737420452Q73656E6365030E3Q0052617370696E672053637265616D03113Q004272616D626C6574686F726E20436F617403123Q004E6F75726973682074686520466F7265737403143Q005374696D756C61746520526573697374616E636503163Q005374696D756C61746520526567656E65726174696F6E030C3Q0052657061697220466C657368030C3Q00447261696E20466C75696473030C3Q00476F726573706C612Q74657203083Q00426F6E656D656E64030D3Q004275726E696E67204C69676874030A3Q0042612Q746C6520437279030B3Q0043696E646572626C617374030D3Q00506172616E6F6964204D696E64030B3Q00417263696E6720566F6964030E3Q00466C616D696E6720546574686572030E3Q0043612Q6C204461726B737061776E030C3Q0047726561746572204865616C030B3Q00546F78696320426C2Q6F6D03103Q00526573746F72696E67204D6574616C73030E3Q0043656E736F72696E67204765617203113Q00456E736E6172696E6720536861646F7773030F3Q00546F726D656E74696E67204265616D030B3Q00566F696420566F2Q6C6579030C3Q0056656E6F6D20566F2Q6C657903103Q005265736F6E616E742042612Q7261676503113Q00486F2Q72696679696E6720536872692Q6C030B3Q00506F69736F6E20426F6C74030E3Q00426F696C696E6720466C616D6573030C3Q00486F6E657920566F2Q6C657903123Q0052656A7576656E6174696E6720486F6E657903113Q0053696C6B656E20526573747261696E7473030F3Q004772696D776561766520426C617374030B3Q004D656E64696E6720576562030C3Q0053696C6B2042696E64696E67030E3Q0054776973742054686F7567687473030F3Q004669726562612Q6C20566F2Q6C6579030D3Q005069657263696E67205761696C03083Q00576562205772617003103Q005265766F6C74696E6720566F2Q6C6579030C3Q00486F776C696E672046656172030C3Q004162792Q73616C20486F776C030C3Q0053696C6B656E205368652Q6C030B3Q004D612Q73205472656D6F72030C3Q005374696E6B7920566F6D697403103Q005374616C6B696E6720536861646F7773030B3Q004E6574686572205269667403083Q00526567696369646503093Q00566F696420426F6C74030E3Q00457870756C73696F6E204265616D030B3Q0053696C6B656E20546F6D6203013Q007203013Q006703013Q0062026Q10703F026Q10803F026Q18883F026Q10903F026Q14943F025Q00AAA440024Q0018401C41024Q0080E20941024Q00E073E940024Q0014511741024Q00A0D4F240025Q00708E40024Q00E02QED40025Q00EAF240025Q0044BF40030B3Q004372656174654672616D6503053Q004672616D6503153Q004865726F526F746174696F6E5F4F6F634672616D6503083Q005549506172656E7403073Q0053657453697A65026Q33E33F03083Q00536574506F696E7403073Q00544F504C454654030E3Q005365744672616D6553747261746103043Q004849474803043Q004869646503073Q0054657874757265030D3Q004372656174655465787475726503073Q004F5645524C4159030C3Q00536574412Q6C506F696E7473030F3Q00536574436F6C6F7254657874757265026Q00F03F030D3Q0052656769737465724576656E74030C3Q00412Q444F4E5F4C4F4144454403153Q00504C415945525F454E544552494E475F574F524C44030C3Q00504C415945525F4C4F47494E03093Q0053657453637269707403073Q004F6E4576656E7403093Q004E65775469636B6572026Q00E03F026Q00084003063Q0053657441504C025Q008070400098013Q006F3Q00023Q001227000200013Q002065000200020002001227000300033Q001227000400043Q002065000500030005002065000600050006002065000700050007002065000800050008002065000900050009002065000A0003000A002065000B0003000B002065000C0003000C001227000D000D3Q001227000E000E3Q001227000F000F3Q001227001000103Q001227001100113Q0020650012001100120020650013001100130020650014001100140020650015001100150020650016001100160020650016001600170020650016001600180020650017001100160020650017001700170020650017001700190012270018001A3Q0012270019001B3Q00206500190019001C001227001A001D3Q002065001A001A001E001227001B001F3Q002065001C000A0020002065001C001C0021002065001D000C0020002065001D001D00212Q000C001E5Q002065001F001D002200204E001F001F00232Q007B001F00204Q0030001E3Q0001002065001F00110016002065001F001F00170020650020001100160020650020002000202Q000C00213Q00050020650022001100250020650022002200240010080021002400220020650022001100250020650022002200260020650022002200200020650022002200160010080021001600220020650022001100250020650022002200260020650022002200200020650022002200270010080021002700220020650022001100250020650022002200260020650022002200200020650022002200280010080021002800220020650022001100250020650022002200260020650022002200200020650022002200210010080021002100222Q0076002200363Q001237003700293Q00065B00383Q000100132Q003F3Q00064Q003F3Q001E4Q003F3Q00374Q003F3Q001A4Q003F3Q00384Q003F3Q00284Q003F3Q00294Q003F3Q002A4Q003F3Q002B4Q003F3Q002C4Q003F3Q002E4Q003F3Q00304Q003F3Q002D4Q003F3Q002F4Q003F3Q00314Q003F3Q00324Q003F3Q00334Q003F3Q00344Q003F3Q00353Q000228003900013Q00065B003A0002000100012Q003F3Q000F3Q000228003B00033Q002065003C00110025002065003C003C0026002065003C003C0020002065003C003C0021002065003C003C002A002065003C003C002B002065003D00110025002065003D003D0026002065003D003D0020002065003D003D0021002065003D003D002A002065003D003D002C2Q000C003E3Q0005003047003E002D002E003047003E002F002E003047003E0030002E003047003E0031002E003047003E0032002E00065B003F0004000100012Q003F3Q00063Q00065B00400005000100012Q003F3Q00033Q00065B00410006000100032Q003F3Q00064Q003F3Q00214Q003F3Q00033Q00065B00420007000100062Q003F3Q00034Q003F3Q001C4Q003F3Q00114Q003F3Q00124Q003F3Q00404Q003F3Q00414Q000C00436Q000C00443Q001F00304700440033002E00304700440034002E00304700440035002E00304700440036002E00304700440037002E00304700440038002E00304700440039002E0030470044003A002E0030470044003B002E0030470044003C002E0030470044003D002E0030470044003E002E0030470044003F002E00304700440040002E00304700440041002E00304700440042002E00304700440043002E00304700440044002E00304700440045002E00304700440046002E00304700440047002E00304700440048002E00304700440049002E0030470044004A002E0030470044004B002E0030470044004C002E0030470044004D002E0030470044004E002E0030470044004F002E00304700440050002E00304700440051002E00304700440052002E00304700440053002E00304700440054002E00304700440055002E00304700440056002E00304700440057002E00304700440058002E00304700440059002E0030470044005A002E0030470044005B002E0030470044005C002E0030470044005D002E0030470044005E002E0030470044005F002E00304700440060002E00304700440061002E00304700440062002E00304700440063002E00304700440064002E00304700440065002E00304700440066002E00304700440067002E00304700440068002E00304700440069002E0030470044006A002E0030470044006B002E00065B00450008000100082Q003F3Q00114Q003F3Q00064Q003F3Q00034Q003F3Q00104Q003F3Q00444Q003F3Q001C4Q003F3Q00124Q003F3Q00433Q00065B00460009000100062Q003F3Q000D4Q003F3Q00054Q003F3Q000E4Q003F3Q00034Q003F3Q00114Q003F3Q001E3Q00065B0047000A000100012Q003F3Q00033Q00065B0048000B000100042Q003F3Q00034Q003F3Q00114Q003F3Q001C4Q003F3Q00473Q00065B0049000C000100052Q003F3Q00064Q003F3Q00214Q003F3Q00034Q003F3Q001C4Q003F3Q00123Q00065B004A000D000100062Q003F3Q001C4Q003F3Q00114Q003F3Q00064Q003F3Q00124Q003F3Q00034Q003F3Q001B3Q00065B004B000E000100052Q003F3Q00094Q003F3Q00214Q003F3Q00064Q003F3Q001C4Q003F3Q00123Q00065B004C000F0001000B2Q003F3Q000D4Q003F3Q00054Q003F3Q000E4Q003F3Q00144Q003F3Q003B4Q003F3Q00214Q003F3Q001C4Q003F3Q00124Q003F3Q00114Q003F3Q00064Q003F3Q00393Q00065B004D00100001000A2Q003F3Q000D4Q003F3Q00054Q003F3Q000E4Q003F3Q00094Q003F3Q001C4Q003F3Q00064Q003F3Q00214Q003F3Q00124Q003F3Q000F4Q003F3Q003A3Q00065B004E0011000100042Q003F3Q00084Q003F3Q00064Q003F3Q001C4Q003F3Q00124Q000C004F3Q00052Q000C00503Q00030030470050006C00290030470050006D00290030470050006E006F001008004F002D00502Q000C00503Q00030030470050006C00290030470050006D00290030470050006E0070001008004F002F00502Q000C00503Q00030030470050006C00290030470050006D00290030470050006E0071001008004F003000502Q000C00503Q00030030470050006C00290030470050006D00290030470050006E0072001008004F003100502Q000C00503Q00030030470050006C00290030470050006D00290030470050006E0073001008004F003200502Q000C0050000A3Q001237005100743Q001237005200753Q001237005300763Q001237005400773Q001237005500783Q001237005600793Q0012370057007A3Q0012370058007B3Q0012370059007C3Q001237005A007D4Q00010050000A00010012270051007E3Q0012370052007F3Q001237005300803Q001227005400814Q002D00510054000200204E005200510082001237005400833Q001237005500834Q001E00520055000100204E005200510084001237005400854Q001E00520054000100204E005200510086001237005400874Q001E00520054000100204E0052005100882Q006700520002000100204E00520051008A2Q0076005400543Q0012370055008B4Q002D00520055000200100800510089005200206500520051008900204E00530052008C2Q0078005500514Q001E00530055000100204E00530052008D0012370055008E3Q0012370056008E3Q0012370057008E3Q0012370058008E4Q001E0053005800012Q000C00535Q000228005400123Q00065B00550013000100012Q003F3Q00543Q00065B00560014000100012Q003F3Q00113Q00065B00570015000100072Q003F3Q00514Q003F3Q00114Q003F3Q00564Q003F3Q00504Q003F3Q00534Q003F3Q00554Q003F3Q00523Q00065B00580016000100022Q003F3Q00114Q003F3Q00573Q0012270059007E3Q001237005A007F4Q000E00590002000200204E005A0059008F001237005C00904Q001E005A005C000100204E005A0059008F001237005C00914Q001E005A005C000100204E005A0059008F001237005C00924Q001E005A005C000100204E005A00590093001237005C00943Q00065B005D0017000100022Q003F3Q00584Q003F3Q00574Q001E005A005D0001001227005A001D3Q002065005A005A0095001237005B00963Q00065B005C0018000100032Q003F3Q00114Q003F3Q00584Q003F3Q00574Q001E005A005C0001001227005A001D3Q002065005A005A001E001237005B00973Q00065B005C0019000100022Q003F3Q00584Q003F3Q00574Q001E005A005C000100065B005A001A000100142Q003F3Q00114Q003F3Q00384Q003F3Q000D4Q003F3Q00054Q003F3Q000E4Q003F3Q00064Q003F3Q00144Q003F3Q001F4Q003F3Q00034Q003F3Q00084Q003F3Q00424Q003F3Q00494Q003F3Q00484Q003F3Q00454Q003F3Q00464Q003F3Q004A4Q003F3Q004B4Q003F3Q004C4Q003F3Q004D4Q003F3Q004E3Q00065B005B001B000100012Q003F3Q00113Q002065005C00110098001237005D00994Q0078005E005A4Q0078005F005B4Q001E005C005F00012Q002A3Q00013Q001C3Q000D3Q00030E3Q004765745472696E6B657444617461026Q00144003023Q004944028Q0003073Q005370652Q6C494403063Q00557361626C65026Q00F03F03063Q004F626A65637403053Q005370652Q6C03053Q0052616E676503083Q004361737454696D6503083Q00432Q6F6C646F776E03083Q004578636C75646564003F9Q003Q00204E5Q00014Q000200014Q001B3Q000200014Q000200023Q002Q26000200220001000200040A3Q0022000100206500023Q000300261F000200190001000400040A3Q0019000100206500020001000300261F000200190001000400040A3Q0019000100206500023Q0005000E15000400130001000200040A3Q0013000100206500023Q000600062C0002001900013Q00040A3Q00190001002065000200010005000E15000400220001000200040A3Q00220001002065000200010006000648000200220001000100040A3Q002200014Q000200023Q0020580002000200072Q005E000200026Q000200033Q001237000300023Q00065B00043Q000100012Q00333Q00044Q001E0002000400012Q002A3Q00013Q00206500023Q00082Q005E000200053Q0020650002000100082Q005E000200063Q00206500023Q00032Q005E000200073Q0020650002000100032Q005E000200083Q00206500023Q00092Q005E000200093Q00206500023Q000A2Q005E0002000A3Q00206500023Q000B2Q005E0002000B3Q0020650002000100092Q005E0002000C3Q00206500020001000A2Q005E0002000D3Q00206500020001000B2Q005E0002000E3Q00206500023Q000C2Q005E0002000F3Q00206500020001000C2Q005E000200103Q00206500023Q000D2Q005E000200113Q00206500020001000D2Q005E000200124Q002A3Q00013Q00018Q00039Q004Q00413Q000100012Q002A3Q00017Q00063Q00025Q0040594003053Q00706169727303063Q00457869737473030D3Q004973446561644F7247686F737403093Q004973496E52616E676503103Q004865616C746850657263656E74616765021C3Q001237000300013Q001227000400024Q007800056Q001600040002000600040A3Q0018000100204E0009000800032Q000E00090002000200062C0009001800013Q00040A3Q0018000100204E0009000800042Q000E000900020002000648000900180001000100040A3Q0018000100204E0009000800052Q0078000B00014Q002D0009000B000200062C0009001800013Q00040A3Q0018000100204E0009000800062Q000E00090002000200066E000900180001000300040A3Q001800012Q0078000300094Q0078000200083Q000632000400050001000200040A3Q000500012Q0002000200024Q002A3Q00017Q00063Q0003053Q00706169727303063Q00457869737473030D3Q004973446561644F7247686F737403093Q004973496E52616E676503063Q00556E6974494403043Q0054414E4B021C3Q001227000200014Q007800036Q001600020002000400040A3Q0017000100204E0007000600022Q000E00070002000200062C0007001700013Q00040A3Q0017000100204E0007000600032Q000E000700020002000648000700170001000100040A3Q0017000100204E0007000600042Q0078000900014Q002D00070009000200062C0007001700013Q00040A3Q001700014Q00075Q0020650008000600052Q000E000700020002002650000700170001000600040A3Q001700012Q0002000600023Q000632000200040001000200040A3Q000400012Q0076000200024Q0002000200024Q002A3Q00017Q000B3Q00028Q0003053Q007061697273030A3Q00556E6974457869737473030C3Q00556E69744973467269656E6403063Q00706C6179657203113Q00556E69744973446561644F7247686F7374030B3Q00556E6974496E52616E6765030A3Q00556E69744865616C7468030D3Q00556E69744865616C74684D6178026Q005940026Q00F03F03293Q001237000300013Q001227000400024Q007800056Q001600040002000600040A3Q00250001001227000900034Q0078000A00074Q000E00090002000200062C0009002500013Q00040A3Q00250001001227000900043Q001237000A00054Q0078000B00074Q002D0009000B000200062C0009002500013Q00040A3Q00250001001227000900064Q0078000A00074Q000E000900020002000648000900250001000100040A3Q00250001001227000900074Q0078000A00074Q000E00090002000200062C0009002500013Q00040A3Q00250001001227000900084Q0078000A00074Q000E000900020002001227000A00094Q0078000B00074Q000E000A000200022Q002400090009000A00205900090009000A00066B000900250001000200040A3Q0025000100205800030003000B000632000400050001000200040A3Q000500012Q0002000300024Q002A3Q00017Q00063Q00028Q00026Q00F03F03113Q00476574456E656D696573496E52616E676503063Q00457869737473030D3Q004973446561644F7247686F737403093Q0043616E412Q7461636B01203Q001237000100013Q001237000200026Q00035Q00204E0003000300032Q007800056Q002D0003000500022Q0003000300033Q001237000400023Q00040D0002001E00014Q00065Q00204E0006000600032Q007800086Q002D0006000800022Q004300060006000500204E0007000600042Q000E00070002000200062C0007001D00013Q00040A3Q001D000100204E0007000600052Q000E0007000200020006480007001D0001000100040A3Q001D00014Q00075Q00204E0007000700062Q0078000900064Q002D00070009000200062C0007001D00013Q00040A3Q001D000100205800010001000200045D0002000900012Q0002000100024Q002A3Q00017Q00063Q00030C3Q0047726F75704D656D62657273028Q0003053Q00706169727303063Q0045786973747303103Q004865616C746850657263656E74616765025Q00805640001D9Q003Q0020655Q000100062C3Q001A00013Q00040A3Q001A00019Q000020655Q00012Q00037Q000E150002001A00013Q00040A3Q001A00010012273Q00036Q00015Q0020650001000100012Q00163Q0002000200040A3Q0018000100204E0005000400042Q000E00050002000200062C0005001800013Q00040A3Q0018000100204E0005000400052Q000E000500020002002Q26000500180001000600040A3Q001800012Q006A00056Q0002000500023Q0006323Q000E0001000200040A3Q000E00012Q006A3Q00014Q00023Q00024Q002A3Q00017Q000E3Q00030F3Q00412Q66656374696E67436F6D626174030B3Q00526573746F726174696F6E03133Q004F6F634865616C696E675468726573686F6C64025Q00805640030A3Q00556E697445786973747303053Q00666F63757303043Q00556E6974030A3Q00556E69744973556E697403063Q00706C6179657203103Q004865616C746850657263656E7461676503063Q00457869737473030D3Q004973446561644F7247686F737403093Q004973496E52616E6765026Q004440003C9Q003Q00204E5Q00012Q000E3Q0002000200062C3Q000700013Q00040A3Q000700012Q006A8Q00023Q00028Q00013Q0020655Q00020020655Q00030006483Q000D0001000100040A3Q000D00010012373Q00043Q001227000100053Q001237000200064Q000E00010002000200062C0001003900013Q00040A3Q003900014Q000100023Q002065000100010007001237000200064Q000E000100020002001227000200083Q001237000300063Q001237000400094Q002D00020004000200062C0002002500013Q00040A3Q002500014Q00025Q00204E00020002000A2Q000E00020002000200064D0002000200013Q00040A3Q002200012Q002300026Q006A000200014Q0002000200023Q00040A3Q0039000100204E00020001000B2Q000E00020002000200062C0002003900013Q00040A3Q0039000100204E00020001000C2Q000E000200020002000648000200390001000100040A3Q0039000100204E00020001000D0012370004000E4Q002D00020004000200062C0002003900013Q00040A3Q0039000100204E00020001000A2Q000E00020002000200064D0002000200013Q00040A3Q003700012Q002300026Q006A000200014Q0002000200024Q006A00016Q0002000100024Q002A3Q00017Q001C3Q0003043Q00556E697403063Q00706C6179657203073Q00536B796675727903093Q0047686F7374576F6C66030B3Q0047554953652Q74696E67732Q033Q0041504C03063Q005368616D616E03073Q00436F2Q6D6F6E7303073Q00536B794675727903073Q0049735265616479030D3Q006F6E6C7920636865636B20757303063Q0042752Q66557003223Q0043617374696E6720536B796675727920546F74656D202873656C6620636865636B2903113Q00636865636B2077686F6C652067726F7570030C3Q0047726F75704D656D62657273028Q0003053Q00706169727303063Q0045786973747303233Q0043617374696E6720536B796675727920546F74656D202867726F757020636865636B2903083Q004175746F576F6C66030F3Q00412Q66656374696E67436F6D62617403083Q0049734D6F76696E67030A3Q0049734361737461626C65030E3Q004F6E6C7920696E20436F6D62617403123Q004F6E6C79206F7574206F6620636F6D62617403063Q00616C77617973030F3Q00556E697443617374696E67496E666F03123Q0043617374696E672047686F737420576F6C6600849Q003Q0020655Q0001001237000100024Q000E3Q000200024Q000100013Q0020650001000100034Q000200013Q0020650002000200044Q000300023Q0020650003000300050020650003000300060020650003000300070020650003000300080020650003000300094Q000400013Q00206500040004000300204E00040004000A2Q000E00040002000200062C0004004E00013Q00040A3Q004E0001002650000300250001000B00040A3Q0025000100204E00043Q000C4Q000600013Q0020650006000600032Q002D000400060002000648000400250001000100040A3Q002500014Q000400036Q000500013Q0020650005000500032Q000E00040002000200062C0004004E00013Q00040A3Q004E00010012370004000D4Q0002000400023Q00040A3Q004E00010026500003004E0001000E00040A3Q004E00012Q006A000400016Q00055Q00206500050005000F00062C0005004400013Q00040A3Q004400014Q00055Q00206500050005000F2Q0003000500053Q000E15001000440001000500040A3Q00440001001227000500116Q00065Q00206500060006000F2Q001600050002000700040A3Q0042000100204E000A000900122Q000E000A0002000200062C000A004200013Q00040A3Q0042000100204E000A0009000C4Q000C00013Q002065000C000C00032Q002D000A000C000200062C000A004200013Q00040A3Q004200012Q006A00045Q00040A3Q00440001000632000500360001000200040A3Q0036000100062C0004004E00013Q00040A3Q004E00014Q000500036Q000600013Q0020650006000600032Q000E00050002000200062C0005004E00013Q00040A3Q004E0001001237000500134Q0002000500026Q000400023Q00206500040004000500206500040004000600206500040004000700206500040004000800206500040004001400204E00053Q00152Q000E00050002000200204E00063Q00162Q000E00060002000200204E00073Q000C4Q000900013Q0020650009000900042Q002D0007000900024Q000800013Q00206500080008000400204E0008000800172Q000E00080002000200062C0008008300013Q00040A3Q00830001000648000700830001000100040A3Q00830001002650000400680001001800040A3Q006800010006480005006E0001000100040A3Q006E00010026500004006C0001001900040A3Q006C000100062C0005006E00013Q00040A3Q006E0001002650000400830001001A00040A3Q008300010012270008001B3Q001237000900024Q000E000800020002000648000800830001000100040A3Q008300014Q000800044Q002900080001000200062C0008008300013Q00040A3Q008300014Q000800054Q0029000800010002000648000800830001000100040A3Q008300014Q000800036Q000900013Q0020650009000900042Q000E00080002000200062C0008008300013Q00040A3Q008300010012370008001C4Q0002000800024Q002A3Q00017Q00233Q00030E3Q0047554953652Q74696E677347657403093Q00496E74652Q72757074030D3Q004175746F496E74652Q72757074030F3Q004973496E44756E67656F6E4172656103123Q00496E74652Q72757074496E44756E67656F6E03043Q004E6F6E6503043Q00556E697403063Q0074617267657403063Q0045786973747303063Q00706C6179657203093Q004973496E52616E6765026Q003E40030F3Q00556E697443617374696E67496E666F030F3Q00556E69744368612Q6E656C496E666F03093Q0057686974656C697374030E3Q004361737450657263656E74616765030C3Q0049734368612Q6E656C696E6703093Q00497343617374696E6703173Q00496E74652Q7275707450657263656E744368612Q6E656C03103Q00496E74652Q7275707450657263656E7403093Q0057696E64536865617203073Q004973526561647903253Q0043617374696E672057696E64205368656172206F6E20696E74652Q7275707469626C653A2003083Q004175746F5374756E026Q00F03F027Q0040026Q00084003073Q0049734B6E6F776E030A3Q0049734361737461626C65030F3Q004661696C656420746F20636173742003043Q004E616D65030B3Q005374756E207370652Q6C20030D3Q00206973206E6F74206B6E6F776E03103Q00206973206E6F74206361737461626C6503123Q0020636F6E646974696F6E206E6F74206D657400BA9Q003Q0020655Q00012Q00293Q0001000200206500013Q0002002065000100010002002065000200010003000648000200090001000100040A3Q000900012Q002A3Q00016Q000200013Q00204E0002000200042Q000E00020002000200062C0002001200013Q00040A3Q00120001002065000200010005002650000200120001000600040A3Q001200012Q002A3Q00016Q000200023Q002065000200020007001237000300084Q000E00020002000200204E0003000200092Q000E00030002000200062C000300B900013Q00040A3Q00B900014Q000300033Q0012370004000A3Q001237000500084Q002D00030005000200062C000300B900013Q00040A3Q00B9000100204E00030002000B0012370005000C4Q002D00030005000200062C000300B900013Q00040A3Q00B900010012270003000D3Q001237000400084Q001600030002000A000648000300340001000100040A3Q00340001001227000B000E3Q001237000C00084Q0016000B000200112Q0078000A00114Q0078000900104Q00780009000F4Q00780009000E4Q00780009000D4Q00780009000C4Q00780003000B3Q00062C0003003800013Q00040A3Q0038000100062C000A003900013Q00040A3Q003900012Q002A3Q00014Q006A000B00016Q000C00013Q00204E000C000C00042Q000E000C0002000200062C000C004700013Q00040A3Q00470001002065000C00010005002650000C00470001000F00040A3Q004700014Q000C00044Q0043000C000C0003000653000B00470001000C00040A3Q004700012Q006A000B5Q000648000B004A0001000100040A3Q004A00012Q002A3Q00013Q00204E000C000200102Q000E000C0002000200204E000D000200112Q000E000D0002000200204E000E000200122Q000E000E0002000200062C000D005700013Q00040A3Q00570001002065000F0001001300066E000C005F0001000F00040A3Q005F00012Q002A3Q00013Q00040A3Q005F000100062C000E005E00013Q00040A3Q005E0001002065000F0001001400066E000C005F0001000F00040A3Q005F00012Q002A3Q00013Q00040A3Q005F00012Q002A3Q00016Q000F00053Q002065000F000F001500204E000F000F00162Q000E000F0002000200062C000F006F00013Q00040A3Q006F00014Q000F00066Q001000053Q0020650010001000152Q000E000F0002000200062C000F006F00013Q00040A3Q006F0001001237000F00174Q0078001000034Q0018000F000F00102Q0002000F00023Q002065000F0001001800062C000F00B900013Q00040A3Q00B90001001237000F00196Q001000074Q0003001000103Q001237001100193Q00040D000F00B900014Q001300074Q00430013001300120020650013001300194Q001400074Q004300140014001200206500140014001A4Q001500074Q004300150015001200206500150015001B00204E00160013001C2Q000E001600020002000648001600870001000100040A3Q0087000100204E00160013001C2Q006A001800014Q002D00160018000200204E00170013001D2Q000E0017000200022Q0078001800154Q002900180001000200062C0016009E00013Q00040A3Q009E000100062C0017009E00013Q00040A3Q009E000100062C0018009E00013Q00040A3Q009E00014Q001900064Q0078001A00134Q000E00190002000200062C0019009800013Q00040A3Q009800012Q0002001400023Q00040A3Q00B800010012370019001E3Q00204E001A0013001F2Q000E001A000200022Q001800190019001A2Q0002001900023Q00040A3Q00B80001000648001600A70001000100040A3Q00A70001001237001900203Q00204E001A0013001F2Q000E001A00020002001237001B00214Q001800190019001B2Q0002001900023Q00040A3Q00B80001000648001700B00001000100040A3Q00B00001001237001900203Q00204E001A0013001F2Q000E001A00020002001237001B00224Q001800190019001B2Q0002001900023Q00040A3Q00B80001000648001800B80001000100040A3Q00B80001001237001900203Q00204E001A0013001F2Q000E001A00020002001237001B00234Q001800190019001B2Q0002001900023Q00045D000F007700012Q002A3Q00017Q00283Q0003043Q005261696403053Q005061727479028Q00026Q00F03F03053Q00706169727303063Q00457869737473030D3Q004973446561644F7247686F737403093Q004973496E52616E6765026Q00444003103Q004865616C746850657263656E74616765026Q00594003123Q00476574496E76656E746F72794974656D494403063Q00706C61796572026Q002A40026Q002C4003043Q004974656D030B3Q0047554953652Q74696E67732Q033Q0041504C03063Q005368616D616E030B3Q00526573746F726174696F6E03093Q00432Q6F6C646F776E73030B3Q005472696E6B657431557365030A3Q005472696E6B657431485003073Q004973526561647903023Q004944030A3Q0057697468204C6F67696303043Q0043617374031C3Q005573696E67205472696E6B65742031202857697468204C6F67696329030E3Q005769746820432Q6F6C646F776E7303123Q004865726F526F746174696F6E43686172444203073Q00546F2Q676C6573026Q00084003203Q005573696E67205472696E6B6574203120285769746820432Q6F6C646F776E732903183Q005769746820432Q6F6C646F776E7320616E64204C6F676963032A3Q005573696E67205472696E6B6574203120285769746820432Q6F6C646F776E7320616E64204C6F67696329030B3Q005472696E6B657432557365030A3Q005472696E6B6574324850031C3Q005573696E67205472696E6B65742032202857697468204C6F6769632903203Q005573696E67205472696E6B6574203220285769746820432Q6F6C646F776E7329032A3Q005573696E67205472696E6B6574203220285769746820432Q6F6C646F776E7320616E64204C6F6769632900DC9Q004Q00293Q0001000200062C3Q000800013Q00040A3Q000800016Q00013Q0020655Q00010006483Q000A0001000100040A3Q000A00016Q00013Q0020655Q00024Q000100024Q0029000100010002000E15000300120001000100040A3Q001200014Q000100024Q0029000100010002000648000100130001000100040A3Q00130001001237000100043Q001237000200033Q001237000300033Q001227000400054Q007800056Q001600040002000600040A3Q002A000100204E0009000800062Q000E00090002000200062C0009002A00013Q00040A3Q002A000100204E0009000800072Q000E0009000200020006480009002A0001000100040A3Q002A000100204E000900080008001237000B00094Q002D0009000B000200062C0009002A00013Q00040A3Q002A000100204E00090008000A2Q000E0009000200022Q0005000200020009002058000300030004000632000400190001000200040A3Q00190001000E15000300310001000300040A3Q003100012Q0024000400020003000648000400320001000100040A3Q003200010012370004000B4Q0076000500063Q0012270007000C3Q0012370008000D3Q0012370009000E4Q002D0007000900020012270008000C3Q0012370009000D3Q001237000A000F4Q002D0008000A000200062C0007004300013Q00040A3Q004300014Q000900033Q0020650009000900102Q0078000A00074Q000E0009000200022Q0078000500093Q00040A3Q0043000100062C0008004B00013Q00040A3Q004B00014Q000900033Q0020650009000900102Q0078000A00084Q000E0009000200022Q0078000600093Q00040A3Q004B00014Q000900043Q0020650009000900110020650009000900120020650009000900130020650009000900140020650009000900150020650009000900164Q000A00043Q002065000A000A0011002065000A000A0012002065000A000A0013002065000A000A0014002065000A000A0015002065000A000A001700062C0005009300013Q00040A3Q0093000100204E000B000500182Q000E000B0002000200062C000B009300013Q00040A3Q009300014Q000B00053Q00204E000C000500192Q000E000C000200022Q0043000B000B000C000648000B00930001000100040A3Q00930001002650000900720001001A00040A3Q0072000100066B000400720001000A00040A3Q007200014Q000B00043Q002065000B000B001B2Q0078000C00054Q000E000B0002000200062C000B009300013Q00040A3Q00930001001237000B001C4Q0002000B00023Q00040A3Q00930001002650000900820001001D00040A3Q00820001001227000B001E3Q002065000B000B001F002065000B000B002000062C000B008200013Q00040A3Q008200014Q000B00043Q002065000B000B001B2Q0078000C00054Q000E000B0002000200062C000B009300013Q00040A3Q00930001001237000B00214Q0002000B00023Q00040A3Q00930001002650000900930001002200040A3Q0093000100066B000400930001000A00040A3Q00930001001227000B001E3Q002065000B000B001F002065000B000B002000062C000B009300013Q00040A3Q009300014Q000B00043Q002065000B000B001B2Q0078000C00054Q000E000B0002000200062C000B009300013Q00040A3Q00930001001237000B00234Q0002000B00026Q000B00043Q002065000B000B0011002065000B000B0012002065000B000B0013002065000B000B0014002065000B000B0015002065000B000B00244Q000C00043Q002065000C000C0011002065000C000C0012002065000C000C0013002065000C000C0014002065000C000C0015002065000C000C002500062C000600DB00013Q00040A3Q00DB000100204E000D000600182Q000E000D0002000200062C000D00DB00013Q00040A3Q00DB00014Q000D00053Q00204E000E000600192Q000E000E000200022Q0043000D000D000E000648000D00DB0001000100040A3Q00DB0001002650000B00BA0001001A00040A3Q00BA000100066B000400BA0001000C00040A3Q00BA00014Q000D00043Q002065000D000D001B2Q0078000E00064Q000E000D0002000200062C000D00DB00013Q00040A3Q00DB0001001237000D00264Q0002000D00023Q00040A3Q00DB0001002650000B00CA0001001D00040A3Q00CA0001001227000D001E3Q002065000D000D001F002065000D000D002000062C000D00CA00013Q00040A3Q00CA00014Q000D00043Q002065000D000D001B2Q0078000E00064Q000E000D0002000200062C000D00DB00013Q00040A3Q00DB0001001237000D00274Q0002000D00023Q00040A3Q00DB0001002650000B00DB0001002200040A3Q00DB000100066B000400DB0001000C00040A3Q00DB0001001227000D001E3Q002065000D000D001F002065000D000D002000062C000D00DB00013Q00040A3Q00DB00014Q000D00043Q002065000D000D001B2Q0078000E00064Q000E000D0002000200062C000D00DB00013Q00040A3Q00DB0001001237000D00284Q0002000D00024Q002A3Q00017Q00063Q00026Q00F03F03073Q004D4158494D554D030B3Q00435F556E6974417572617303143Q00476574446562752Q66446174614279496E646578030A3Q0064697370656C4E616D6503053Q006C6F776572021D3Q001237000200016Q00035Q002065000300030002001237000400013Q00040D0002001A0001001227000600033Q0020650006000600042Q007800076Q0078000800054Q002D0006000800020006480006000E0001000100040A3Q000E00012Q006A00076Q0002000700023Q00206500070006000500062C0007001900013Q00040A3Q0019000100204E0008000700062Q000E00080002000200204E0009000100062Q000E000900020002000660000800190001000900040A3Q001900012Q006A000800014Q0002000800023Q00045D0002000500012Q006A00026Q0002000200024Q002A3Q00017Q00153Q0003043Q00556E697403053Q00666F63757303063Q00457869737473030B3Q0047554953652Q74696E67732Q033Q0041504C03063Q005368616D616E030B3Q00526573746F726174696F6E03073Q0044697370652Q6C030D3Q0044697370652Q6C506F69736F6E030C3Q0044697370652Q6C4D61676963030C3Q0044697370652Q6C437572736503143Q00506F69736F6E436C65616E73696E67546F74656D030A3Q0049734361737461626C6503063Q00506F69736F6E03043Q0043617374032F3Q0043617374696E6720506F69736F6E20436C65616E73696E6720546F74656D206F6E20506F69736F6E20446562752Q66030C3Q0050757269667953706972697403053Q004D6167696303053Q00437572736503193Q0043617374696E672050757269667920537069726974206F6E2003073Q0020446562752Q66005E9Q003Q0020655Q0001001237000100024Q000E3Q0002000200204E00013Q00032Q000E000100020002000648000100090001000100040A3Q000900012Q002A3Q00016Q000100013Q002065000100010004002065000100010005002065000100010006002065000100010007002065000100010008000648000100120001000100040A3Q001200012Q000C00015Q00206500020001000900206500030001000A00206500040001000B00062C0002002C00013Q00040A3Q002C00014Q000500023Q00206500050005000C00204E00050005000D2Q000E00050002000200062C0005002C00013Q00040A3Q002C00014Q000500033Q001237000600023Q0012370007000E4Q002D00050007000200062C0005002C00013Q00040A3Q002C00014Q000500013Q00206500050005000F4Q000600023Q00206500060006000C2Q000E00050002000200062C0005002C00013Q00040A3Q002C0001001237000500104Q0002000500023Q000648000300300001000100040A3Q0030000100062C0004005D00013Q00040A3Q005D00014Q000500023Q00206500050005001100204E00050005000D2Q000E00050002000200062C0005005D00013Q00040A3Q005D000100062C0003003E00013Q00040A3Q003E00014Q000500033Q001237000600023Q001237000700124Q002D000500070002000648000500460001000100040A3Q0046000100062C0004005D00013Q00040A3Q005D00014Q000500033Q001237000600023Q001237000700134Q002D00050007000200062C0005005D00013Q00040A3Q005D00014Q000500013Q00206500050005000F4Q000600023Q0020650006000600112Q0076000700084Q007800096Q002D00050009000200062C0005005D00013Q00040A3Q005D0001001237000500146Q000600033Q001237000700023Q001237000800124Q002D00060008000200062C0006005900013Q00040A3Q00590001001237000600123Q0006480006005A0001000100040A3Q005A0001001237000600133Q001237000700154Q00180005000500072Q0002000500024Q002A3Q00017Q001B3Q0003123Q004865726F526F746174696F6E43686172444203073Q00546F2Q676C6573026Q001C40030F3Q00412Q66656374696E67436F6D62617403083Q0049734D6F76696E67030B3Q00526573746F726174696F6E03133Q004F6F634865616C696E675468726573686F6C64030A3Q00556E697445786973747303053Q00666F63757303043Q00556E6974030A3Q00556E69744973556E697403063Q00706C6179657203103Q004865616C746850657263656E7461676503063Q00457869737473030D3Q004973446561644F7247686F737403093Q004973496E52616E6765026Q00444003093Q004F6352697074696465030A3Q0049734361737461626C6503153Q0043617374696E67204F6352697074696465206F6E20030A3Q004F6F634865616C696E67030D3Q0052697074696465485375726765030E3Q004F634865616C696E675375726765031A3Q0043617374696E67204F634865616C696E675375726765206F6E20030C3Q00526970746964654857617665030D3Q004F634865616C696E675761766503193Q0043617374696E67204F634865616C696E6757617665206F6E2000773Q0012273Q00013Q0020655Q00020020655Q00030006483Q00060001000100040A3Q000600012Q002A3Q00019Q003Q00204E5Q00042Q000E3Q0002000200062C3Q000C00013Q00040A3Q000C00012Q002A3Q00019Q003Q00204E5Q00052Q000E3Q000200022Q0076000100016Q000200013Q002065000200020006002065000200020007001227000300083Q001237000400094Q000E00030002000200062C0003003B00013Q00040A3Q003B00014Q000300023Q00206500030003000A001237000400094Q000E0003000200020012270004000B3Q001237000500093Q0012370006000C4Q002D00040006000200062C0004002900013Q00040A3Q002900014Q00045Q00204E00040004000D2Q000E00040002000200066B0004003B0001000200040A3Q003B00014Q00015Q00040A3Q003B000100204E00040003000E2Q000E00040002000200062C0004003B00013Q00040A3Q003B000100204E00040003000F2Q000E0004000200020006480004003B0001000100040A3Q003B000100204E000400030010001237000600114Q002D00040006000200062C0004003B00013Q00040A3Q003B000100204E00040003000D2Q000E00040002000200066B0004003B0001000200040A3Q003B00012Q0078000100033Q0006480001003E0001000100040A3Q003E00012Q002A3Q00016Q000300033Q00206500030003001200204E0003000300132Q000E00030002000200062C0003004C00013Q00040A3Q004C00014Q000300046Q000400033Q0020650004000400122Q000E00030002000200062C0003004C00013Q00040A3Q004C0001001237000300144Q0002000300026Q000300013Q002065000300030006002065000300030015002650000300620001001600040A3Q006200014Q000400033Q00206500040004001700204E0004000400132Q000E00040002000200062C0004006200013Q00040A3Q006200010006483Q00620001000100040A3Q006200014Q000400046Q000500033Q0020650005000500172Q000E00040002000200062C0004007400013Q00040A3Q00740001001237000400184Q0002000400023Q00040A3Q00740001002650000300740001001900040A3Q007400014Q000400033Q00206500040004001A00204E0004000400132Q000E00040002000200062C0004007400013Q00040A3Q007400010006483Q00740001000100040A3Q007400014Q000400046Q000500033Q00206500050005001A2Q000E00040002000200062C0004007400013Q00040A3Q007400010012370004001B4Q0002000400024Q0076000400044Q0002000400024Q002A3Q00017Q00203Q00030B3Q0041737472616C5368696674030A3Q0049734361737461626C65030B3Q0047554953652Q74696E67732Q033Q0041504C03063Q005368616D616E030B3Q00526573746F726174696F6E030D3Q0041737472616C53686966744850026Q00494003103Q004865616C746850657263656E7461676503113Q0041737472616C205368696674206361737403113Q0053746F6E6542756C7761726B546F74656D03143Q0055736553746F6E6542756C7761726B546F74656D03183Q0053746F6E652042756C7761726B20546F74656D2063617374030B3Q004561727468536869656C6403073Q0045536869656C6403113Q004361737445736869656C644F6E54616E6B030A3Q00556E697445786973747303053Q00666F63757303043Q00556E6974030A3Q00556E69744973556E697403063Q00706C6179657203063Q0042752Q66557003133Q004561727468536869656C6453656C6642752Q6603273Q00456172746820536869656C642063617374206F6E20706C61796572202876696120666F6375732903193Q00456172746820536869656C642063617374206F6E2074616E6B03123Q0053706972697477616C6B657273477261636503083Q0049734D6F76696E6703133Q00556E6974412Q66656374696E67436F6D62617403193Q0053706972697477616C6B65722773204772616365206361737403113Q0045617274686C6976696E67576561706F6E024Q00804F224103173Q0045617274686C6976696E6720576561706F6E206361737400D09Q003Q0020655Q000100204E5Q00022Q000E3Q0002000200062C3Q001C00013Q00040A3Q001C00016Q00013Q0020655Q00030020655Q00040020655Q00050020655Q00060020655Q00070006483Q000F0001000100040A3Q000F00010012373Q00086Q000100023Q00204E0001000100092Q000E00010002000200066B0001001C00013Q00040A3Q001C00014Q000100036Q00025Q0020650002000200012Q000E00010002000200062C0001001C00013Q00040A3Q001C00010012370001000A4Q0002000100029Q003Q0020655Q000B00204E5Q00022Q000E3Q0002000200062C3Q004000013Q00040A3Q004000016Q00013Q0020655Q00030020655Q00040020655Q00050020655Q00060020655Q000C00062C3Q004000013Q00040A3Q004000016Q00013Q0020655Q00030020655Q00040020655Q00050020655Q00060020655Q000B0006483Q00330001000100040A3Q003300010012373Q00086Q000100023Q00204E0001000100092Q000E00010002000200066B0001004000013Q00040A3Q004000014Q000100036Q00025Q00206500020002000B2Q000E00010002000200062C0001004000013Q00040A3Q004000010012370001000D4Q0002000100029Q003Q0020655Q000E00204E5Q00022Q000E3Q0002000200062C3Q008E00013Q00040A3Q008E00016Q00013Q0020655Q00030020655Q00040020655Q00050020655Q00060020655Q000F0006483Q004F0001000100040A3Q004F00010012373Q00086Q000100013Q002065000100010003002065000100010004002065000100010005002065000100010006002065000100010010001227000200113Q001237000300124Q000E00020002000200062C0002008E00013Q00040A3Q008E00014Q000200043Q002065000200020013001237000300124Q000E00020002000200062C0001007A00013Q00040A3Q007A0001001227000300143Q001237000400123Q001237000500154Q002D00030005000200062C0003007A00013Q00040A3Q007A000100204E0003000200092Q000E00030002000200066B0003008E00013Q00040A3Q008E00014Q000300023Q00204E0003000300164Q00055Q0020650005000500172Q002D0003000500020006480003008E0001000100040A3Q008E00014Q000300036Q00045Q00206500040004000E2Q000E00030002000200062C0003008E00013Q00040A3Q008E0001001237000300184Q0002000300023Q00040A3Q008E000100062C0001008E00013Q00040A3Q008E000100204E0003000200092Q000E00030002000200066B0003008E00013Q00040A3Q008E000100204E0003000200164Q00055Q00206500050005000E2Q002D0003000500020006480003008E0001000100040A3Q008E00014Q000300036Q00045Q00206500040004000E2Q000E00030002000200062C0003008E00013Q00040A3Q008E0001001237000300194Q0002000300029Q003Q0020655Q001A00204E5Q00022Q000E3Q0002000200062C3Q00AE00013Q00040A3Q00AE00016Q00013Q0020655Q00030020655Q00040020655Q00050020655Q00060020655Q001A00062C3Q00AE00013Q00040A3Q00AE00016Q00023Q00204E5Q001B2Q000E3Q0002000200062C3Q00AE00013Q00040A3Q00AE00010012273Q001C3Q001237000100154Q000E3Q0002000200062C3Q00AE00013Q00040A3Q00AE00016Q00036Q00015Q00206500010001001A2Q000E3Q0002000200062C3Q00AE00013Q00040A3Q00AE00010012373Q001D4Q00023Q00029Q003Q0020655Q001E00204E5Q00022Q000E3Q0002000200062C3Q00CF00013Q00040A3Q00CF00016Q00013Q0020655Q00030020655Q00040020655Q00050020655Q00060020655Q001E00062C3Q00CF00013Q00040A3Q00CF00010012273Q001C3Q001237000100154Q000E3Q000200020006483Q00CF0001000100040A3Q00CF00016Q00054Q007A3Q0001000100062C3Q00C700013Q00040A3Q00C70001002Q26000100CF0001001F00040A3Q00CF00014Q000200036Q00035Q00206500030003001E2Q000E00020002000200062C000200CF00013Q00040A3Q00CF0001001237000200204Q0002000200024Q002A3Q00017Q00143Q0003063Q00457869737473030D3Q004973446561644F7247686F737403103Q004865616C746850657263656E74616765030B3Q00526573746F726174696F6E03073Q004865616C696E6703043Q004E534850026Q004E40030F3Q005768696368556E64756C6174696F6E03063Q0042752Q66557003103Q004E61747572657353776966746E652Q7303113Q0054696D6553696E63654C61737443617374026Q00E03F030C3Q004865616C696E672057617665030B3Q004865616C696E6757617665030A3Q0049734361737461626C6503353Q0043617374696E67204865616C696E67205761766520287769746820616374697665204E617475726527732053776966746E652Q7329030D3Q004865616C696E67205375726765030C3Q004865616C696E67537572676503363Q0043617374696E67204865616C696E6720537572676520287769746820616374697665204E617475726527732053776966746E652Q732903303Q0043617374696E67204E617475726527732053776966746E652Q7320666F7220456D657267656E6379204865616C696E6700656Q00015Q00204E0001000100012Q000E00010002000200062C0001000B00013Q00040A3Q000B00014Q00015Q00204E0001000100022Q000E0001000200020006480001000B0001000100040A3Q000B00019Q000006483Q000E0001000100040A3Q000E00012Q002A3Q00013Q00204E00013Q00032Q000E0001000200024Q000200013Q002065000200020004002065000200020005002065000200020006000648000200170001000100040A3Q00170001001237000200076Q000300013Q0020650003000300040020650003000300050020650003000300084Q000400023Q00204E0004000400094Q000600033Q00206500060006000A2Q002D000400060002000648000400280001000100040A3Q002800014Q000400033Q00206500040004000A00204E00040004000B2Q000E000400020002002Q260004004D0001000C00040A3Q004D00010026500003003B0001000D00040A3Q003B00014Q000400033Q00206500040004000E00204E00040004000F2Q000E00040002000200062C0004003B00013Q00040A3Q003B00014Q000400046Q000500033Q00206500050005000E2Q0076000600074Q007800086Q002D00040008000200062C0004004D00013Q00040A3Q004D0001001237000400104Q0002000400023Q00040A3Q004D00010026500003004D0001001100040A3Q004D00014Q000400033Q00206500040004001200204E00040004000F2Q000E00040002000200062C0004004D00013Q00040A3Q004D00014Q000400046Q000500033Q0020650005000500122Q0076000600074Q007800086Q002D00040008000200062C0004004D00013Q00040A3Q004D0001001237000400134Q0002000400023Q00066B000100640001000200040A3Q006400014Q000400033Q00206500040004000A00204E00040004000F2Q000E00040002000200062C0004006400013Q00040A3Q006400014Q000400023Q00204E0004000400094Q000600033Q00206500060006000A2Q002D000400060002000648000400640001000100040A3Q006400014Q000400046Q000500033Q00206500050005000A2Q000E00040002000200062C0004006400013Q00040A3Q00640001001237000400144Q0002000400024Q002A3Q00017Q004F3Q0003043Q005261696403053Q005061727479028Q00026Q00F03F026Q004440030B3Q00526573746F726174696F6E2Q033Q00416F45030C3Q005370697269744C696E6B4850030F3Q005370697269744C696E6B546F74656D030A3Q0049734361737461626C65030F3Q005370697269744C696E6B436F756E7403273Q0043617374696E6720537069726974204C696E6B20546F74656D2028416F45204865616C696E6729030D3Q004865616C696E6754696465485003103Q004865616C696E6754696465546F74656D03103Q004865616C696E6754696465436F756E7403283Q0043617374696E67204865616C696E67205469646520546F74656D2028416F45204865616C696E6729030C3Q00417363656E64616E6365485003093Q00432Q6F6C646F776E73030D3Q00557365417363656E64616E636503083Q004E6F742055736564030A3Q0057697468204C6F676963030F3Q00417363656E64616E6365436F756E74030A3Q00417363656E64616E6365032B3Q0043617374696E6720417363656E64616E63652028416F45204865616C696E672077697468204C6F67696329030E3Q005769746820432Q6F6C646F776E7303123Q004865726F526F746174696F6E43686172444203073Q00546F2Q676C6573026Q000840032F3Q0043617374696E6720417363656E64616E63652028416F45204865616C696E67207769746820432Q6F6C646F776E732903183Q005769746820432Q6F6C646F776E7320616E64204C6F67696303393Q0043617374696E6720417363656E64616E63652028416F45204865616C696E67207769746820432Q6F6C646F776E7320616E64204C6F6769632903043Q004147485003053Q00557365414703073Q004147436F756E7403113Q00416E6365737472616C47756964616E636503333Q0043617374696E6720416E6365737472616C2047756964616E63652028416F45204865616C696E672077697468204C6F6769632903373Q0043617374696E6720416E6365737472616C2047756964616E63652028416F45204865616C696E67207769746820432Q6F6C646F776E732903413Q0043617374696E6720416E6365737472616C2047756964616E63652028416F45204865616C696E67207769746820432Q6F6C646F776E7320616E64204C6F67696329030B3Q0047554953652Q74696E67732Q033Q0041504C03063Q005368616D616E03103Q004865616C696E675261696E436F756E74030D3Q004865616C696E675261696E4850030C3Q0053757267696E67546F74656D03233Q0043617374696E672053757267696E6720546F74656D2028416F45204865616C696E6729030B3Q004865616C696E675261696E03223Q0043617374696E67204865616C696E67205261696E2028416F45204865616C696E6729030C3Q00436C6F75644275727374485003123Q00436C6F756442757273745265636173744850030F3Q00436C6F75646275727374546F74656D030B3Q004973417661696C61626C65030F3Q00436C6F75644275727374436F756E7403263Q0043617374696E6720436C6F7564627572737420546F74656D2028416F45204865616C696E672903063Q0042752Q66557003153Q00436C6F75644275727374526563617374436F756E7403283Q00526563617374696E6720436C6F7564627572737420546F74656D2028416F45204865616C696E672903123Q004865616C696E6753747265616D546F74656D032A3Q0043617374696E67204865616C696E672053747265616D20546F74656D2028416F45204865616C696E6729032C3Q00526563617374696E67204865616C696E672053747265616D20546F74656D2028416F45204865616C696E6729030D3Q004561727468656E57612Q6C485003103Q004561727468656E57612Q6C546F74656D03103Q004561727468656E57612Q6C436F756E7403283Q0043617374696E67204561727468656E2057612Q6C20546F74656D2028416F45204865616C696E6729030C3Q0057652Q6C737072696E674850030A3Q0057652Q6C737072696E67030F3Q0057652Q6C737072696E67436F756E7403203Q0043617374696E672057652Q6C737072696E672028416F45204865616C696E6729030A3Q00446F776E706F7572485003083Q00446F776E706F7572030D3Q00446F776E706F7572436F756E74031E3Q0043617374696E6720446F776E706F75722028416F45204865616C696E672903083Q00486967687469646503133Q00436861696E4865616C4869676854696465485003093Q00436861696E4865616C03163Q00436861696E4865616C4869676854696465436F756E74032B3Q0043617374696E6720436861696E204865616C20284869676820546964652C20416F45204865616C696E6729030B3Q00436861696E4865616C4850030E3Q00436861696E4865616C436F756E7403203Q0043617374696E6720436861696E204865616C2028416F45204865616C696E6729002A029Q003Q00293Q0001000200062C3Q000800013Q00040A3Q000800016Q00013Q0020655Q00010006483Q000A0001000100040A3Q000A00016Q00013Q0020655Q00024Q000100024Q0029000100010002000E15000300120001000100040A3Q001200014Q000100024Q0029000100010002000648000100130001000100040A3Q00130001001237000100046Q000200034Q0029000200010002000648000200180001000100040A3Q001800012Q002A3Q00016Q000200044Q007800035Q001237000400056Q000500053Q0020650005000500060020650005000500070020650005000500082Q002D0002000500024Q000300063Q00206500030003000900204E00030003000A2Q000E00030002000200062C0003003400013Q00040A3Q003400014Q000300053Q00206500030003000600206500030003000700206500030003000B00066B000300340001000200040A3Q003400014Q000300076Q000400063Q0020650004000400092Q000E00030002000200062C0003003400013Q00040A3Q003400010012370003000C4Q0002000300026Q000300044Q007800045Q001237000500056Q000600053Q00206500060006000600206500060006000700206500060006000D2Q002D0003000600024Q000400063Q00206500040004000E00204E00040004000A2Q000E00040002000200062C0004005000013Q00040A3Q005000014Q000400053Q00206500040004000600206500040004000700206500040004000F00066B000400500001000300040A3Q005000014Q000400076Q000500063Q00206500050005000E2Q000E00040002000200062C0004005000013Q00040A3Q00500001001237000400104Q0002000400026Q000400044Q007800055Q001237000600056Q000700053Q0020650007000700060020650007000700070020650007000700112Q002D0004000700024Q000500053Q0020650005000500060020650005000500120020650005000500130026500005005F0001001400040A3Q005F000100040A3Q00A10001002650000500760001001500040A3Q007600014Q000600053Q00206500060006000600206500060006000700206500060006001600066B000600760001000400040A3Q007600014Q000600063Q00206500060006001700204E00060006000A2Q000E00060002000200062C0006007600013Q00040A3Q007600014Q000600076Q000700063Q0020650007000700172Q000E00060002000200062C000600A100013Q00040A3Q00A10001001237000600184Q0002000600023Q00040A3Q00A10001002650000500860001001900040A3Q008600010012270006001A3Q00206500060006001B00206500060006001C00062C0006008600013Q00040A3Q008600014Q000600076Q000700063Q0020650007000700172Q000E00060002000200062C000600A100013Q00040A3Q00A100010012370006001D4Q0002000600023Q00040A3Q00A10001002650000500A10001001E00040A3Q00A100014Q000600053Q00206500060006000600206500060006000700206500060006001600066B000600A10001000400040A3Q00A100010012270006001A3Q00206500060006001B00206500060006001C00062C000600A100013Q00040A3Q00A100014Q000600063Q00206500060006001700204E00060006000A2Q000E00060002000200062C000600A100013Q00040A3Q00A100014Q000600076Q000700063Q0020650007000700172Q000E00060002000200062C000600A100013Q00040A3Q00A100010012370006001F4Q0002000600026Q000600044Q007800075Q001237000800056Q000900053Q0020650009000900060020650009000900070020650009000900202Q002D0006000900024Q000700053Q002065000700070006002065000700070012002065000700070021002650000700B00001001400040A3Q00B0000100040A3Q00E60001002650000700C10001001500040A3Q00C100014Q000800053Q00206500080008000600206500080008000700206500080008002200066B000800C10001000600040A3Q00C100014Q000800076Q000900063Q0020650009000900232Q000E00080002000200062C000800E600013Q00040A3Q00E60001001237000800244Q0002000800023Q00040A3Q00E60001002650000700D10001001900040A3Q00D100010012270008001A3Q00206500080008001B00206500080008001C00062C000800D100013Q00040A3Q00D100014Q000800076Q000900063Q0020650009000900232Q000E00080002000200062C000800E600013Q00040A3Q00E60001001237000800254Q0002000800023Q00040A3Q00E60001002650000700E60001001E00040A3Q00E600014Q000800053Q00206500080008000600206500080008000700206500080008002200066B000800E60001000600040A3Q00E600010012270008001A3Q00206500080008001B00206500080008001C00062C000800E600013Q00040A3Q00E600014Q000800076Q000900063Q0020650009000900232Q000E00080002000200062C000800E600013Q00040A3Q00E60001001237000800264Q0002000800026Q000800083Q00206500080008002700206500080008002800206500080008002900206500080008000600206500080008000700206500080008002A4Q000900083Q00206500090009002700206500090009002800206500090009002900206500090009000600206500090009000700206500090009002B4Q000A00044Q0078000B5Q001237000C00054Q0078000D00094Q002D000A000D000200066B000800182Q01000A00040A3Q00182Q014Q000B00063Q002065000B000B002C00204E000B000B000A2Q000E000B0002000200062C000B000A2Q013Q00040A3Q000A2Q014Q000B00076Q000C00063Q002065000C000C002C2Q000E000B0002000200062C000B00182Q013Q00040A3Q00182Q01001237000B002D4Q0002000B00023Q00040A3Q00182Q014Q000B00063Q002065000B000B002E00204E000B000B000A2Q000E000B0002000200062C000B00182Q013Q00040A3Q00182Q014Q000B00076Q000C00063Q002065000C000C002E2Q000E000B0002000200062C000B00182Q013Q00040A3Q00182Q01001237000B002F4Q0002000B00026Q000B00044Q0078000C5Q001237000D00056Q000E00053Q002065000E000E0006002065000E000E0007002065000E000E00302Q002D000B000E00024Q000C00044Q0078000D5Q001237000E00056Q000F00053Q002065000F000F0006002065000F000F0007002065000F000F00312Q002D000C000F00024Q000D00063Q002065000D000D003200204E000D000D00332Q000E000D0002000200062C000D005E2Q013Q00040A3Q005E2Q014Q000D00063Q002065000D000D003200204E000D000D000A2Q000E000D0002000200062C000D00422Q013Q00040A3Q00422Q014Q000D00053Q002065000D000D0006002065000D000D0007002065000D000D003400066B000D00422Q01000B00040A3Q00422Q014Q000D00076Q000E00063Q002065000E000E00322Q000E000D0002000200062C000D00422Q013Q00040A3Q00422Q01001237000D00354Q0002000D00026Q000D00063Q002065000D000D003200204E000D000D000A2Q000E000D0002000200062C000D00862Q013Q00040A3Q00862Q014Q000D00093Q00204E000D000D00364Q000F00063Q002065000F000F00322Q002D000D000F000200062C000D00862Q013Q00040A3Q00862Q014Q000D00053Q002065000D000D0006002065000D000D0007002065000D000D003700066B000D00862Q01000C00040A3Q00862Q014Q000D00076Q000E00063Q002065000E000E00322Q000E000D0002000200062C000D00862Q013Q00040A3Q00862Q01001237000D00384Q0002000D00023Q00040A3Q00862Q014Q000D00063Q002065000D000D003900204E000D000D000A2Q000E000D0002000200062C000D00722Q013Q00040A3Q00722Q014Q000D00053Q002065000D000D0006002065000D000D0007002065000D000D003400066B000D00722Q01000B00040A3Q00722Q014Q000D00076Q000E00063Q002065000E000E00392Q000E000D0002000200062C000D00722Q013Q00040A3Q00722Q01001237000D003A4Q0002000D00026Q000D00063Q002065000D000D003900204E000D000D000A2Q000E000D0002000200062C000D00862Q013Q00040A3Q00862Q014Q000D00053Q002065000D000D0006002065000D000D0007002065000D000D003700066B000D00862Q01000C00040A3Q00862Q014Q000D00076Q000E00063Q002065000E000E00392Q000E000D0002000200062C000D00862Q013Q00040A3Q00862Q01001237000D003B4Q0002000D00026Q000D00044Q0078000E5Q001237000F00056Q001000053Q00206500100010000600206500100010000700206500100010003C2Q002D000D001000024Q000E00063Q002065000E000E003D00204E000E000E000A2Q000E000E0002000200062C000E00A22Q013Q00040A3Q00A22Q014Q000E00053Q002065000E000E0006002065000E000E0007002065000E000E003E00066B000E00A22Q01000D00040A3Q00A22Q014Q000E00076Q000F00063Q002065000F000F003D2Q000E000E0002000200062C000E00A22Q013Q00040A3Q00A22Q01001237000E003F4Q0002000E00026Q000E00044Q0078000F5Q001237001000056Q001100053Q0020650011001100060020650011001100070020650011001100402Q002D000E001100024Q000F00063Q002065000F000F004100204E000F000F000A2Q000E000F0002000200062C000F00BE2Q013Q00040A3Q00BE2Q014Q000F00053Q002065000F000F0006002065000F000F0007002065000F000F004200066B000F00BE2Q01000E00040A3Q00BE2Q014Q000F00076Q001000063Q0020650010001000412Q000E000F0002000200062C000F00BE2Q013Q00040A3Q00BE2Q01001237000F00434Q0002000F00026Q000F00044Q007800105Q001237001100056Q001200053Q0020650012001200060020650012001200070020650012001200442Q002D000F001200024Q001000063Q00206500100010004500204E00100010000A2Q000E00100002000200062C001000DA2Q013Q00040A3Q00DA2Q014Q001000053Q00206500100010000600206500100010000700206500100010004600066B001000DA2Q01000F00040A3Q00DA2Q014Q001000076Q001100063Q0020650011001100452Q000E00100002000200062C001000DA2Q013Q00040A3Q00DA2Q01001237001000474Q0002001000026Q001000093Q00204E0010001000364Q001200063Q0020650012001200482Q002D00100012000200062C0010000502013Q00040A3Q000502014Q001000044Q007800115Q001237001200056Q001300053Q0020650013001300060020650013001300070020650013001300492Q002D0010001300024Q001100063Q00206500110011004A00204E00110011000A2Q000E00110002000200062C0011000502013Q00040A3Q000502014Q001100053Q00206500110011000600206500110011000700206500110011004B00066B001100050201001000040A3Q000502014Q0011000A4Q007800125Q001237001300054Q002D00110013000200062C0011000502013Q00040A3Q000502014Q001200076Q001300063Q00206500130013004A2Q0076001400154Q0078001600114Q002D00120016000200062C0012000502013Q00040A3Q000502010012370012004C4Q0002001200026Q001000044Q007800115Q001237001200056Q001300053Q00206500130013000600206500130013000700206500130013004D2Q002D0010001300024Q001100063Q00206500110011004A00204E00110011000A2Q000E00110002000200062C0011002902013Q00040A3Q002902014Q001100053Q00206500110011000600206500110011000700206500110011004E00066B001100290201001000040A3Q002902014Q0011000A4Q007800125Q001237001300054Q002D00110013000200062C0011002902013Q00040A3Q002902014Q001200076Q001300063Q00206500130013004A2Q0076001400154Q0078001600114Q002D00120016000200062C0012002902013Q00040A3Q002902010012370012004F4Q0002001200024Q002A3Q00017Q00253Q0003043Q005261696403053Q005061727479028Q00026Q00F03F03063Q00457869737473030D3Q004973446561644F7247686F7374030D3Q004D616E6154696465546F74656D030A3Q0049734361737461626C65030E3Q004D616E6150657263656E74616765030B3Q00526573746F726174696F6E03073Q004865616C696E67030A3Q004D616E61546964654D5003223Q0043617374696E67204D616E61205469646520546F74656D20284C6F77204D616E6129030B3Q00556E6C656173684C69666503103Q004865616C746850657263656E74616765030D3Q00556E6C656173684C696665485003243Q0043617374696E6720556E6C65617368204C6966652028466F637573204865616C696E672903073Q005269707469646503093Q00526970746964654850031F3Q0043617374696E6720526970746964652028466F637573204865616C696E6729030E3Q005072696D6F726469616C57617665030F3Q005072696D6F7264696157617665485003273Q0043617374696E67205072696D6F726469616C20576176652028466F637573204865616C696E672903083Q0074616E6B556E6974030C3Q004865616C696E675375726765030E3Q004865616C696E675375726765485003253Q0043617374696E67204865616C696E672053757267652028466F637573204865616C696E6729030B3Q004865616C696E6757617665030D3Q004865616C696E6757617665485003243Q0043617374696E67204865616C696E6720576176652028466F637573204865616C696E672903063Q00556E6974494403043Q0054414E4B026Q00444003123Q004865616C696E67537572676554616E6B485003243Q0043617374696E67204865616C696E67205375726765202854616E6B204865616C696E672903113Q004865616C696E675761766554616E6B485003233Q0043617374696E67204865616C696E672057617665202854616E6B204865616C696E67290004019Q003Q00293Q0001000200062C3Q000800013Q00040A3Q000800016Q00013Q0020655Q00010006483Q000A0001000100040A3Q000A00016Q00013Q0020655Q00024Q000100024Q0029000100010002000E15000300120001000100040A3Q001200014Q000100024Q0029000100010002000648000100130001000100040A3Q00130001001237000100044Q0076000200026Q000300033Q00204E0003000300052Q000E00030002000200062C0003001F00013Q00040A3Q001F00014Q000300033Q00204E0003000300062Q000E0003000200020006480003001F0001000100040A3Q001F00014Q000200036Q000300043Q00206500030003000700204E0003000300082Q000E00030002000200062C0003003600013Q00040A3Q003600014Q000300053Q00204E0003000300092Q000E0003000200024Q000400063Q00206500040004000A00206500040004000B00206500040004000C00066B000300360001000400040A3Q003600014Q000300076Q000400043Q0020650004000400072Q000E00030002000200062C0003003600013Q00040A3Q003600010012370003000D4Q0002000300026Q000300043Q00206500030003000E00204E0003000300082Q000E00030002000200062C0003005000013Q00040A3Q0050000100062C0002005000013Q00040A3Q0050000100204E00030002000F2Q000E0003000200024Q000400063Q00206500040004000A00206500040004000B00206500040004001000066B000300500001000400040A3Q005000014Q000300076Q000400043Q00206500040004000E2Q0076000500064Q0078000700024Q002D00030007000200062C0003005000013Q00040A3Q00500001001237000300114Q0002000300026Q000300043Q00206500030003001200204E0003000300082Q000E00030002000200062C0003006A00013Q00040A3Q006A000100062C0002006A00013Q00040A3Q006A000100204E00030002000F2Q000E0003000200024Q000400063Q00206500040004000A00206500040004000B00206500040004001300066B0003006A0001000400040A3Q006A00014Q000300076Q000400043Q0020650004000400122Q0076000500064Q0078000700024Q002D00030007000200062C0003006A00013Q00040A3Q006A0001001237000300144Q0002000300026Q000300043Q00206500030003001500204E0003000300082Q000E00030002000200062C0003008400013Q00040A3Q0084000100062C0002008400013Q00040A3Q0084000100204E00030002000F2Q000E0003000200024Q000400063Q00206500040004000A00206500040004000B00206500040004001600066B000300840001000400040A3Q008400014Q000300076Q000400043Q0020650004000400152Q0076000500064Q0078000700024Q002D00030007000200062C0003008400013Q00040A3Q00840001001237000300174Q0002000300023Q001227000300183Q000648000300A10001000100040A3Q00A100014Q000300043Q00206500030003001900204E0003000300082Q000E00030002000200062C000300A100013Q00040A3Q00A1000100062C000200A100013Q00040A3Q00A1000100204E00030002000F2Q000E0003000200024Q000400063Q00206500040004000A00206500040004000B00206500040004001A00066B000300A10001000400040A3Q00A100014Q000300076Q000400043Q0020650004000400192Q0076000500064Q0078000700024Q002D00030007000200062C000300A100013Q00040A3Q00A100010012370003001B4Q0002000300026Q000300043Q00206500030003001C00204E0003000300082Q000E00030002000200062C000300BE00013Q00040A3Q00BE000100062C000200BE00013Q00040A3Q00BE0001001227000300183Q000648000300BE0001000100040A3Q00BE000100204E00030002000F2Q000E0003000200024Q000400063Q00206500040004000A00206500040004000B00206500040004001D00066B000300BE0001000400040A3Q00BE00014Q000300076Q000400043Q00206500040004001C2Q0076000500064Q0078000700024Q002D00030007000200062C000300BE00013Q00040A3Q00BE00010012370003001E4Q0002000300023Q00062F000300C70001000200040A3Q00C700014Q000300083Q00206500040002001F2Q000E00030002000200261F000300C60001002000040A3Q00C600012Q002300036Q006A000300013Q00062C000300CB00013Q00040A3Q00CB0001000653000400CF0001000200040A3Q00CF00014Q000400094Q007800055Q001237000600214Q002D00040006000200062C000400E900013Q00040A3Q00E900014Q000500043Q00206500050005001900204E0005000500082Q000E00050002000200062C000500E900013Q00040A3Q00E9000100204E00050004000F2Q000E0005000200024Q000600063Q00206500060006000A00206500060006000B00206500060006002200066B000500E90001000600040A3Q00E900014Q000500076Q000600043Q0020650006000600192Q0076000700084Q0078000900044Q002D00050009000200062C000500E900013Q00040A3Q00E90001001237000500234Q0002000500023Q00062C000400032Q013Q00040A3Q00032Q014Q000500043Q00206500050005001C00204E0005000500082Q000E00050002000200062C000500032Q013Q00040A3Q00032Q0100204E00050004000F2Q000E0005000200024Q000600063Q00206500060006000A00206500060006000B00206500060006002400066B000500032Q01000600040A3Q00032Q014Q000500076Q000600043Q00206500060006001C2Q0076000700084Q0078000900044Q002D00050009000200062C000500032Q013Q00040A3Q00032Q01001237000500254Q0002000500024Q002A3Q00017Q00133Q0003063Q00457869737473030D3Q004973446561644F7247686F737403093Q0043616E412Q7461636B03083Q0049734D6F76696E6703093Q00456E656D6965733879026Q000840030E3Q00436861696E4C696768746E696E67030A3Q0049734361737461626C6503243Q0043617374696E6720436861696E204C696768746E696E672028332B205461726765747329030B3Q00466C616D6553686F636B5803083Q00446562752Q66557003103Q00466C616D6553686F636B446562752Q6603133Q0043617374696E6720466C616D652053686F636B030A3Q0046726F737453686F636B032C3Q0043617374696E672046726F73742053686F636B20284D6F76696E672C204E6F20466C616D652053686F636B2903093Q004C617661427572737403223Q0043617374696E67204C617661204275727374202853696E676C652054617267657429030D3Q004C696768746E696E67426F6C7403263Q0043617374696E67204C696768746E696E6720426F6C74202853696E676C65205461726765742900809Q003Q00204E5Q00012Q000E3Q0002000200062C3Q001000013Q00040A3Q001000019Q0000204E5Q00022Q000E3Q000200020006483Q00100001000100040A3Q001000016Q00013Q00204E5Q00034Q00026Q002D3Q000200020006483Q00110001000100040A3Q001100012Q002A3Q00018Q00013Q00204E5Q00042Q000E3Q00020002001227000100054Q0003000100013Q000E68000600280001000100040A3Q002800014Q000100023Q00206500010001000700204E0001000100082Q000E00010002000200062C0001002800013Q00040A3Q002800010006483Q00280001000100040A3Q002800014Q000100036Q000200023Q0020650002000200072Q000E00010002000200062C0001002800013Q00040A3Q00280001001237000100094Q0002000100026Q000100023Q00206500010001000A00204E0001000100082Q000E00010002000200062C0001004300013Q00040A3Q004300014Q00015Q00204E00010001000B4Q000300023Q00206500030003000C2Q002D00010003000200062C0001003B00013Q00040A3Q003B00014Q000100023Q00206500010001000A00204E0001000100082Q000E00010002000200062C0001004300013Q00040A3Q004300014Q000100036Q000200023Q00206500020002000A2Q000E00010002000200062C0001004300013Q00040A3Q004300010012370001000D4Q0002000100026Q000100023Q00206500010001000A00204E0001000100082Q000E000100020002000648000100590001000100040A3Q0059000100062C3Q005900013Q00040A3Q005900014Q000100023Q00206500010001000E00204E0001000100082Q000E00010002000200062C0001005900013Q00040A3Q005900014Q000100036Q000200023Q00206500020002000E2Q000E00010002000200062C0001005900013Q00040A3Q005900010012370001000F4Q0002000100026Q000100023Q00206500010001001000204E0001000100082Q000E00010002000200062C0001006900013Q00040A3Q006900010006483Q00690001000100040A3Q006900014Q000100036Q000200023Q0020650002000200102Q000E00010002000200062C0001006900013Q00040A3Q00690001001237000100114Q0002000100026Q000100023Q00206500010001001200204E0001000100082Q000E00010002000200062C0001007F00013Q00040A3Q007F00014Q000100023Q00206500010001001000204E0001000100082Q000E0001000200020006480001007F0001000100040A3Q007F00010006483Q007F0001000100040A3Q007F00014Q000100036Q000200023Q0020650002000200122Q000E00010002000200062C0001007F00013Q00040A3Q007F0001001237000100134Q0002000100024Q002A3Q00017Q00023Q00024Q00C069D040022Q00C03QFFDF4101063Q00205900013Q000100202500010001000200065B00023Q000100012Q003F3Q00014Q0002000200024Q002A3Q00013Q00013Q00023Q00024Q00C069D040022Q00C03QFFDF4100089Q003Q0020595Q00010020255Q00022Q005E9Q007Q00204B5Q00022Q00023Q00024Q002A3Q00019Q002Q0001106Q00016Q007800026Q000E0001000200022Q0078000200014Q00290002000100022Q0078000300014Q00290003000100022Q0078000400014Q00290004000100022Q000C000500034Q0078000600024Q0078000700034Q0078000800044Q00010005000300012Q0002000500024Q002A3Q00017Q00023Q00030D3Q004D61696E49636F6E4672616D6503023Q004944000E9Q003Q0020655Q000100062C3Q000B00013Q00040A3Q000B00019Q000020655Q00010020655Q000200062C3Q000B00013Q00040A3Q000B00012Q00023Q00023Q00040A3Q000B00012Q00768Q00023Q00024Q002A3Q00017Q00173Q00030D3Q004D61696E49636F6E4672616D6503113Q00436861744672616D653145646974426F7803093Q00497356697369626C6503083Q00486173466F63757303043Q004869646503143Q004143544956455F434841545F454449545F424F5803133Q00556E6974412Q66656374696E67436F6D62617403063Q00706C6179657203123Q004865726F526F746174696F6E43686172444203073Q00546F2Q676C6573026Q001C4003093Q0074436F6E7461696E7303013Q0072026Q00F03F03013Q0067027Q004003013Q0062026Q000840030F3Q00536574436F6C6F7254657874757265030E3Q00436C656172412Q6C506F696E747303083Q00536574506F696E7403073Q00544F504C45465403043Q0053686F77007E9Q003Q00062C3Q000700013Q00040A3Q000700016Q00013Q0020655Q00010006483Q00080001000100040A3Q000800012Q002A3Q00013Q0012273Q00023Q00062C3Q001900013Q00040A3Q001900010012273Q00023Q00204E5Q00032Q000E3Q000200020006483Q00150001000100040A3Q001500010012273Q00023Q00204E5Q00042Q000E3Q0002000200062C3Q001900013Q00040A3Q001900019Q0000204E5Q00052Q00673Q000200012Q002A3Q00013Q0012273Q00063Q00062C3Q002500013Q00040A3Q002500010012273Q00063Q00204E5Q00032Q000E3Q0002000200062C3Q002500013Q00040A3Q002500019Q0000204E5Q00052Q00673Q000200012Q002A3Q00013Q0012273Q00073Q001237000100084Q000E3Q0002000200062C3Q002E00013Q00040A3Q002E00019Q0000204E5Q00052Q00673Q000200012Q002A3Q00018Q00013Q0020655Q000100204E5Q00032Q000E3Q000200020006483Q00380001000100040A3Q003800019Q0000204E5Q00052Q00673Q000200012Q002A3Q00014Q006A8Q0076000100013Q001227000200093Q00062C0002005200013Q00040A3Q00520001001227000200093Q00206500020002000A00062C0002005200013Q00040A3Q00520001001227000200093Q00206500020002000A00206500020002000B00062C0002005200013Q00040A3Q005200014Q000200024Q00290002000100022Q0078000100023Q00062C0001005200013Q00040A3Q005200010012270002000C6Q000300034Q0078000400014Q002D00020004000200062C0002005200013Q00040A3Q005200012Q006A3Q00013Q00062C3Q007A00013Q00040A3Q007A000100062C0001007A00013Q00040A3Q007A00014Q000200044Q0043000200020001000648000200660001000100040A3Q006600014Q000200054Q0078000300014Q000E0002000200024Q000300044Q000C00043Q000300206500050002000E0010080004000D00050020650005000200100010080004000F00050020650005000200120010080004001100052Q00450003000100044Q000200044Q00430002000200014Q000300063Q00204E00030003001300206500050002000D00206500060002000F0020650007000200110012370008000E4Q001E0003000800014Q00035Q00204E0003000300142Q00670003000200014Q00035Q00204E000300030015001237000500164Q001E0003000500014Q00035Q00204E0003000300172Q006700030002000100040A3Q007D00014Q00025Q00204E0002000200052Q00670002000200012Q002A3Q00017Q00063Q00030D3Q004D61696E49636F6E4672616D6503093Q002Q6F63482Q6F6B6564030A3Q0053686F77416374696F6E03043Q0049636F6E030A3Q00536574546578747572652Q0100349Q003Q0020655Q000100062C3Q003300013Q00040A3Q003300019Q000020655Q00010020655Q00020006483Q00330001000100040A3Q003300019Q000020655Q00010020655Q000300062C3Q001800013Q00040A3Q001800019Q000020655Q00010020655Q00034Q00015Q00206500010001000100065B00023Q000100022Q003F8Q00333Q00013Q0010080001000300022Q004A9Q007Q0020655Q00010020655Q000400062C3Q003000013Q00040A3Q003000019Q000020655Q00010020655Q00040020655Q000500062C3Q003000013Q00040A3Q003000019Q000020655Q00010020655Q00040020655Q00054Q00015Q00206500010001000100206500010001000400065B00020001000100032Q003F8Q00338Q00333Q00013Q0010080001000500022Q004A9Q007Q0020655Q00010030473Q000200062Q002A3Q00013Q00023Q00023Q0003073Q005370652Q6C494403023Q004944020F6Q00036Q007800046Q0078000500014Q001900066Q001000033Q000100062C0001000C00013Q00040A3Q000C000100206500030001000100062C0003000C00013Q00040A3Q000C00010020650003000100010010083Q000200034Q000300014Q00410003000100012Q002A3Q00017Q00053Q00030F3Q004765745370652Q6C54657874757265025Q00AAA440024Q00F0501741030D3Q004D61696E49636F6E4672616D6503023Q00494402196Q00036Q007800046Q0078000500014Q001900066Q001000033Q0001001227000300013Q001237000400024Q000E000300020002001227000400013Q001237000500034Q000E000400020002000660000100110001000300040A3Q001100014Q000500013Q00206500050005000400304700050005000200040A3Q00160001000660000100160001000400040A3Q001600014Q000500013Q0020650005000500040030470005000500034Q000500024Q00410005000100012Q002A3Q00017Q00083Q00030C3Q00412Q444F4E5F4C4F41444544030C3Q004865726F526F746174696F6E03073Q00435F54696D657203053Q004166746572026Q00F03F03153Q00504C415945525F454E544552494E475F574F524C44030C3Q00504C415945525F4C4F47494E027Q004003183Q0026500001000C0001000100040A3Q000C00010026500002000C0001000200040A3Q000C0001001227000300033Q002065000300030004001237000400053Q00065B00053Q000100022Q00338Q00333Q00014Q001E00030005000100040A3Q0017000100261F000100100001000600040A3Q00100001002650000100170001000700040A3Q00170001001227000300033Q002065000300030004001237000400083Q00065B00050001000100022Q00338Q00333Q00014Q001E0003000500012Q002A3Q00013Q00028Q00059Q004Q00413Q000100016Q00014Q00413Q000100012Q002A3Q00019Q003Q00059Q004Q00413Q000100016Q00014Q00413Q000100012Q002A3Q00017Q00023Q00030D3Q004D61696E49636F6E4672616D6503093Q002Q6F63482Q6F6B6564000E9Q003Q0020655Q000100062C3Q000B00013Q00040A3Q000B00019Q000020655Q00010020655Q00020006483Q000B0001000100040A3Q000B00016Q00014Q00413Q000100016Q00024Q00413Q000100012Q002A3Q00019Q003Q00059Q004Q00413Q000100016Q00014Q00413Q000100012Q002A3Q00017Q00183Q00030E3Q00496E74652Q72757074436865636B03043Q005261696403053Q005061727479028Q00026Q00F03F030C3Q00456E656D6965734D656C2Q6503163Q00476574456E656D696573496E4D656C2Q6552616E6765026Q00144003093Q00456E656D6965733879026Q00204003113Q00456E656D696573436F756E744D656C2Q65030E3Q00456E656D696573436F756E74387903143Q00456E656D696573436F756E74387953706C617368030D3Q00546172676574497356616C6964030F3Q00412Q66656374696E67436F6D62617403103Q00426F2Q73466967687452656D61696E73030C3Q00466967687452656D61696E73024Q0080B3C540030B3Q00436F6D626F506F696E747303123Q00436F6D626F506F696E747344656669636974030E3Q004973496E4D656C2Q6552616E676503093Q004973496E52616E6765030C3Q004973496E416F4552616E6765030D3Q004973446561644F7247686F737400A79Q003Q00204E5Q00012Q000E3Q0002000200062C3Q000600013Q00040A3Q000600012Q002A3Q00018Q00014Q00413Q000100016Q00024Q00293Q0001000200062C3Q001000013Q00040A3Q001000016Q00033Q0020655Q00020006483Q00120001000100040A3Q001200016Q00033Q0020655Q00034Q000100044Q0029000100010002000E150004001A0001000100040A3Q001A00014Q000100044Q00290001000100020006480001001B0001000100040A3Q001B0001001237000100056Q000200053Q00204E000200020007001237000400084Q002D00020004000200124F000200066Q000200053Q00204E0002000200070012370004000A4Q002D00020004000200124F000200096Q000200064Q002900020001000200062C0002003300013Q00040A3Q00330001001227000200064Q0003000200023Q00124F0002000B3Q001227000200094Q0003000200023Q00124F0002000C3Q001227000200094Q0003000200023Q00124F0002000D3Q00040A3Q00390001001237000200053Q00124F0002000B3Q001237000200053Q00124F0002000C3Q001237000200053Q00124F0002000D6Q000200073Q00206500020002000E2Q0029000200010002000648000200430001000100040A3Q004300014Q000200053Q00204E00020002000F2Q000E00020002000200062C0002006400013Q00040A3Q006400014Q000200083Q0020650002000200102Q002900020001000200124F000200103Q001227000200103Q00124F000200113Q001227000200113Q002650000200520001001200040A3Q005200014Q000200083Q002065000200020011001227000300094Q006A00046Q002D00020004000200124F000200116Q000200053Q00204E0002000200132Q000E00020002000200124F000200136Q000200053Q00204E0002000200142Q000E00020002000200124F000200146Q000200093Q00204E000200020016001237000400084Q002D00020004000200124F000200156Q000200093Q00204E0002000200160012370004000A4Q002D00020004000200124F000200176Q000200053Q00204E0002000200182Q000E000200020002000648000200A60001000100040A3Q00A600012Q0076000200026Q0003000A4Q00290003000100022Q0078000200033Q00062C0002007000013Q00040A3Q007000012Q0002000200026Q0003000B4Q00290003000100022Q0078000200033Q00062C0002007600013Q00040A3Q007600012Q0002000200026Q0003000C4Q00290003000100022Q0078000200033Q00062C0002007C00013Q00040A3Q007C00012Q0002000200026Q0003000D4Q00290003000100022Q0078000200033Q00062C0002008200013Q00040A3Q008200012Q0002000200026Q0003000E4Q00290003000100022Q0078000200033Q00062C0002008800013Q00040A3Q008800012Q0002000200026Q0003000F4Q00290003000100022Q0078000200033Q00062C0002008E00013Q00040A3Q008E00012Q0002000200026Q000300104Q00290003000100022Q0078000200033Q00062C0002009400013Q00040A3Q009400012Q0002000200026Q000300114Q00290003000100022Q0078000200033Q00062C0002009A00013Q00040A3Q009A00012Q0002000200026Q000300124Q00290003000100022Q0078000200033Q00062C000200A000013Q00040A3Q00A000012Q0002000200026Q000300134Q00290003000100022Q0078000200033Q00062C000200A600013Q00040A3Q00A600012Q0002000200024Q002A3Q00017Q00023Q0003053Q005072696E7403383Q00526573746F726174696F6E205368616D616E20726F746174696F6E2068617320622Q656E2075706461746564206279206C7561667265616B00059Q003Q0020655Q0001001237000100024Q00673Q000200012Q002A3Q00017Q00", GetFEnv(), ...);
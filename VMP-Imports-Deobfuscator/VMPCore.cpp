#include <Zydis/Zydis.h>

#include <unicorn/unicorn.h>

#include <BlackBone/Process/Process.h>
#include <BlackBone/PE/PEImage.h>
#include <BlackBone/Patterns/PatternSearch.h>

#include "spdlog/spdlog.h"
#include "spdlog/sinks/ansicolor_sink.h"

#include "Core/Utils/StringConversion/StringConversion.h"

#include "Dependencies/argparse.hpp"

#include "Core/Emulator/Emulator.h"
#include "Core/Pe/PeParser.h"
#include "Core/ZydisWrapper/Wrapper.h"

#include "VMPCore.h"

using namespace blackbone;
using namespace blackbone::pe;


namespace
{
	std::uintptr_t FindModuleBaseByAddress(std::uintptr_t Address)
	{
		for (const auto& sModule : ProcessAccessHelp::moduleList)
		{
			const auto Base = static_cast<std::uintptr_t>(sModule.modBaseAddr);
			const auto Size = static_cast<std::uintptr_t>(sModule.modBaseSize);

			if (Address >= Base && Address < Base + Size)
				return Base;
		}

		return 0;
	}

	bool ModuleListContains(const std::vector<std::uintptr_t>& Modules, std::uintptr_t ModuleBase)
	{
		return std::find(Modules.begin(), Modules.end(), ModuleBase) != Modules.end();
	}
}
void FilterAddresses(std::uintptr_t pImageBase, std::uint32_t u32ImageSize, void* pPeBuffer, std::vector<std::uintptr_t>& vecPatternAddresses, std::vector<ptr_t>& vecAddressResults, std::uint32_t u32SectionBase, std::uint32_t u32SectionSize)
{
	std::uintptr_t pCalculatedAddress{};
	S_DisasmWrapper sDisasm{};

	// @note: @colby57: Iterate through the vector of address results.
	for (const auto& temp : vecAddressResults)
	{
		std::uintptr_t pResultItem = static_cast<std::uintptr_t>(temp);
		std::uintptr_t pOffset = pResultItem - pImageBase;
		std::uintptr_t pTargetAddress = reinterpret_cast<std::uintptr_t>(pPeBuffer) + pOffset;

		sDisasm.m_pRuntimeAddr = static_cast<std::uintptr_t>(pResultItem);

		// @note: @colby57: Check if the first byte at the target address is a relative call (0xE8) and disassemble the instruction.
		if (*(unsigned char*)pTargetAddress == 0xE8 && ZydisWrapper::Disasm(sDisasm, pTargetAddress, 5))
		{
			// @note: @colby57: Calculate the absolute address using the disassembled instruction.
			if (pCalculatedAddress = ZydisWrapper::CalculateAbsoluteAddr(sDisasm, 0); pCalculatedAddress == NULL)
				continue;

			// @note: @colby57: Skip addresses that are outside the image boundaries.
			if (pCalculatedAddress > (pImageBase + u32ImageSize) || pCalculatedAddress < pImageBase)
				continue;

			// @note: @colby57: Skip addresses within the specified section boundaries.
			if (pCalculatedAddress >= (pImageBase + u32SectionBase) &&
				pCalculatedAddress <= (pImageBase + u32SectionBase + u32SectionSize))
				continue;

			// @note: @colby57: Add the filtered address to the pattern address list.
			vecPatternAddresses.emplace_back(pResultItem);
		}
	}
}

void VMPCore::ParseModules()
{
	std::set<std::uintptr_t> uniqueModuleSet;

	// @note: @colby57: Iterate through the patch information vector using a range-based for loop.
	for (const auto& sIatPatchInfo : vecPatchInfo)
		// @note: @colby57: Check if the module address is not already in the set.
		uniqueModuleSet.insert(sIatPatchInfo.m_pBaseModule);

	// @note: @colby57: Assign the unique module addresses to vecModuleList.
	vecModuleList.assign(uniqueModuleSet.begin(), uniqueModuleSet.end());
	spdlog::info("Module count: {}\n", vecModuleList.size());
}

void VMPCore::GetModulePathByAddress(std::uintptr_t Address, ModuleInfo& sTargetModule)
{
	// @note: @colby57: Iterate through the module list using const reference.
	for (const auto& sModule : ProcessAccessHelp::moduleList)
	{
		// @note: @colby57: Check if the module base address matches the provided address.
		if (sModule.modBaseAddr == Address)
		{
			// @note: @colby57: Assign the module information to the target module.
			sTargetModule = sModule;
			return;
		}
	}
}

void VMPCore::ParseApiList()
{
	// @note: @colby57: Iterate through the module list.
	for (const auto& pImportModule : vecModuleList)
	{
		std::set<std::uintptr_t> sEchmoduleApiSet;

		// @note: @colby57: Iterate through the patch information vector using a range-based loop.
		for (const auto& sIatPatchInfo : vecPatchInfo)
		{
			// @note: @colby57: Destructure the struct for better readability.
			const auto [ApiAddress, BaseModule] = std::tie(sIatPatchInfo.m_pApiAddress, sIatPatchInfo.m_pBaseModule);

			// @note: @colby57: Check if the base module matches the current import module.
			if (BaseModule == pImportModule)
				sEchmoduleApiSet.insert(ApiAddress);
		}

		ModuleInfo sTempModule{};

		// @note: @colby57: Get module path by address and populate sTempModule.
		GetModulePathByAddress(pImportModule, sTempModule);

		// @note: @colby57: Use emplace for more efficient insertion into the map.
		mapImportEchmoduleApi.emplace(pImportModule, std::move(sEchmoduleApiSet));

		char kBuffer[256];
		StringConversion::ToAscii(sTempModule.fullPath, kBuffer, sizeof(kBuffer));

		// @note: @colby57: Display module information in the log.
		spdlog::info("{0} -> {1:x}", kBuffer, pImportModule);
	}
}

bool VMPCore::SetPatchIatAddress()
{
	bool allFound = true;

	for (auto& sIatPatchInfo : vecPatchInfo)
	{
		bool found = false;

		for (std::size_t i = 0; i < k32IatSize; i += sizeof(std::uintptr_t))
		{
			std::uintptr_t data = *reinterpret_cast<std::uintptr_t*>(vecIatBuffer.data() + i);

			if (data == sIatPatchInfo.m_pApiAddress)
			{
				sIatPatchInfo.m_pIatAddress = pIatAddress + i;
				found = true;
				break;
			}
		}

		if (!found)
		{
			spdlog::error("Cannot find api address in new IAT: 0x{0:x}", sIatPatchInfo.m_pApiAddress);
			allFound = false;
		}
	}

	return allFound;
}

static void VMPCore::ApplyPatches()
{
	std::vector<std::uint8_t> vecCode(32);
	int iCodeLen{};

	for (const auto& sIatPatchInfo : vecPatchInfo)
	{
		const auto iCallIatMode = sIatPatchInfo.m_iCallIatMode;

		if (iCallIatMode != VMPCore::CALL_IAT_UNKNOWN)
		{
			if (iCodeLen = ZydisWrapper::AssembleCall(
				vecCode.data(),
				vecCode.size(),
				iCallIatMode,
				sIatPatchInfo.m_pIatAddress,
				sIatPatchInfo.m_pPatchAddress,
				sIatPatchInfo.m_iRegIndex))
			{
				if (iCodeLen == 5 || iCodeLen == 6 || ((iCallIatMode == CALL_IAT_MOV_REG || iCallIatMode == VMPCore::CALL_IAT_MOV_REFERENCE) && iCodeLen == 7))
				{
					auto bufferOffset = sIatPatchInfo.m_pPatchAddress - pImageLoadAddress;
					auto* pDest = reinterpret_cast<std::uint8_t*>(pImageBuffer) + bufferOffset;
					memcpy(pDest, vecCode.data(), iCodeLen);
				}
			}
			else
			{
				spdlog::error("Failed to assemble call from patch address: 0x{0:x}", sIatPatchInfo.m_pPatchAddress);
			}
		}
	}
}

bool VMPCore::RebuildIAT()
{
	int Num{};
	int Index{};

	for (auto ImportEchmoduleApi : mapImportEchmoduleApi)
		Num += ImportEchmoduleApi.second.size();

	Num += vecModuleList.size();

	k32IatSize = Num * sizeof(std::uintptr_t);

	vecIatBuffer.resize(k32IatSize, 0);
	auto* pIatEntries = reinterpret_cast<std::uintptr_t*>(vecIatBuffer.data());

	for (auto ImportEchmoduleApi : mapImportEchmoduleApi)
	{
		auto EachModuleApiSet = ImportEchmoduleApi.second;

		for (auto pApiAddress : EachModuleApiSet)
		{
			pIatEntries[Index] = pApiAddress;
			Index += 1;
		}

		pIatEntries[Index] = 0;
		Index += 1;
	}

	spdlog::info("IAT built: {0:x} bytes, {1} entries", k32IatSize, Index);
	return true;
}

bool VMPCore::PatchCalls()
{
	if (!RebuildIAT())
	{
		spdlog::error("RebuildIAT failed!");
		return false;
	}

	if (!SetPatchIatAddress())
	{
		spdlog::error("SetPatchIatAddress failed!");
		return false;
	}

	// ApplyPatches is deferred to DumpModule where the final IAT RVA is known.
	spdlog::info("Patch info collected: {} patches ready", vecPatchInfo.size());
	return true;
}

std::vector<std::string> GetVmpSections(ProcessMemory& sMemory)
{
	// @note: @colby57: Calculate entropy for the given section
	auto CalculateEntropy = [&](IMAGE_SECTION_HEADER Section)
		{
			const auto CalculatedVirtualAddress = (VMPCore::pImageLoadAddress + Section.VirtualAddress);
			const auto BufferSize = Section.Misc.VirtualSize;

			double Entropy{};

			// @note: @colby57: Read section data into a buffer
			std::vector<std::uint8_t> vecBuffer(BufferSize);
			sMemory.Read(CalculatedVirtualAddress, BufferSize, vecBuffer.data());

			std::map<std::uint8_t, double> mapByteProbabilities;
			std::map<std::uint8_t, int> mapByteFrequencies;

			// @note: @colby57: Calculate byte frequencies in the section
			for (const auto& byte : vecBuffer)
				mapByteFrequencies[byte]++;

			// @note: @colby57: Calculate byte probabilities in the section
			for (const auto& pair : mapByteFrequencies)
				mapByteProbabilities[pair.first] = static_cast<double>(pair.second) / BufferSize;

			// @note: @colby57: Calculate entropy using byte probabilities
			for (const auto& pair : mapByteProbabilities)
				Entropy -= pair.second * log2(pair.second);

			// @note: @colby57: Clear and shrink vectors to free memory
			vecBuffer.clear();
			vecBuffer.shrink_to_fit();

			mapByteFrequencies.clear();
			mapByteProbabilities.clear();

			return Entropy;
		};

	double Entropy{};

	std::vector<std::string> vecVmpSections{};

	// @note: @colby57: Iterate through the process sections
	for (const auto Section : VMPCore::vecProcessSections)
	{
		// @note: @colby57: Check if the section is executable
		if (Section.Characteristics & IMAGE_SCN_MEM_EXECUTE)
		{
			spdlog::info("Section name: {}", (char*)Section.Name);
			spdlog::info("Entropy: {}\n", Entropy = CalculateEntropy(Section));

			// @note: @colby57: Check if entropy indicates a potentially VMP-protected section
			// @note: @colby57: Files protected by VMProtect always show entropy above 7.
			if (Entropy > 7.1 && strcmp(".text", (char*)Section.Name) != 0)
			{
				spdlog::warn("Potentially VMP section: {}\n", (char*)Section.Name);
				vecVmpSections.emplace_back((char*)Section.Name);
			}
		}
	}

	return vecVmpSections;
}

void CollectMovIatReferences(std::uintptr_t pImageBase, std::size_t uImageSize, void* pPeBuffer, const std::vector<ptr_t>& vecAddressResults)

{
	if (pPeBuffer == nullptr)
		return;

	auto* pImage = reinterpret_cast<std::uint8_t*>(pPeBuffer);

	for (const auto& Result : vecAddressResults)
	{
		const auto PatchAddress = static_cast<std::uintptr_t>(Result);

		const auto Offset = PatchAddress - pImageBase;
		auto* pInstruction = pImage + Offset;

		if ((pInstruction[0] != 0x48 && pInstruction[0] != 0x4C) || pInstruction[1] != 0x8B)
			continue;

		S_DisasmWrapper sDisasm{};
		if (!ZydisWrapper::Disasm64(sDisasm, reinterpret_cast<std::uintptr_t>(pInstruction), 7))
			continue;


		if (sDisasm.m_sInstruction.mnemonic != ZYDIS_MNEMONIC_MOV || sDisasm.m_sInstruction.operand_count < 2)
			continue;

		const auto& op = sDisasm.m_sOperands[0];
		if (op.type != ZYDIS_OPERAND_TYPE_REGISTER /*|| op.mem.base != ZYDIS_REGISTER_CS*/)
			continue;

		if (sDisasm.m_sOperands[1].type != ZYDIS_OPERAND_TYPE_MEMORY)
			continue;

		if (!sDisasm.m_sOperands[1].mem.disp.has_displacement)
			continue;

		if (sDisasm.m_sOperands[1].mem.base != ZYDIS_REGISTER_RIP)
			continue;

		const std::uintptr_t RipNext = PatchAddress + sDisasm.m_sInstruction.length;
		const std::int64_t Displacement = sDisasm.m_sOperands[1].mem.disp.value;


		const auto SlotAddress = static_cast<std::uintptr_t>(
			static_cast<std::int64_t>(RipNext) + Displacement
			);

		if (SlotAddress < pImageBase || SlotAddress + sizeof(std::uintptr_t) > pImageBase + uImageSize)
			continue;

		const auto SlotOffset = SlotAddress - pImageBase;


		const auto ApiAddress = *reinterpret_cast<std::uintptr_t*>(pImage + SlotOffset);

		if (ApiAddress == 0)
			continue;

		bool is_suspected = false;
		auto api = VMPCore::sApiReader.getApiByVirtualAddress(ApiAddress, &is_suspected);

		if (api == 0)
			continue;

		if (api->module->modBaseAddr == pImageBase || api->module->modBaseAddr == reinterpret_cast<std::uintptr_t>(pImage))
			continue;


		VMPCore::S_IatPatchInfo PatchInfo{};

		PatchInfo.m_iCallIatMode = VMPCore::CALL_IAT_MOV_REFERENCE;
		PatchInfo.m_pPatchAddress = PatchAddress;
		PatchInfo.m_pBaseModule = api->module->modBaseAddr;
		PatchInfo.m_pApiAddress = ApiAddress;

		PatchInfo.m_iRegIndex = op.reg.value;

		VMPCore::vecPatchInfo.emplace_back(std::move(PatchInfo));
		spdlog::info("MOV IAT reference detected at 0x{0:x} targeting 0x{1:x} - {2}", PatchAddress, ApiAddress, api->name);
	}
}


void CollectDirectIatCalls(std::uintptr_t pImageBase, std::size_t uImageSize, void* pPeBuffer, const std::vector<ptr_t>& vecAddressResults)
{
	if (pPeBuffer == nullptr)
		return;

	auto* pImage = reinterpret_cast<std::uint8_t*>(pPeBuffer);

	for (const auto& Result : vecAddressResults)
	{
		const auto PatchAddress = static_cast<std::uintptr_t>(Result);

		if (PatchAddress < pImageBase || PatchAddress + 6 > pImageBase + uImageSize)
			continue;

		const auto Offset = PatchAddress - pImageBase;
		auto* pInstruction = pImage + Offset;

		if (pInstruction[0] != 0xFF || pInstruction[1] != 0x15)
			continue;

		const auto Displacement = *reinterpret_cast<std::int32_t*>(pInstruction + 2);
		const auto RipNext = PatchAddress + 6;
		const auto SlotAddressSigned = static_cast<std::int64_t>(RipNext) + static_cast<std::int64_t>(Displacement);

		if (SlotAddressSigned < 0)
			continue;

		const auto SlotAddress = static_cast<std::uintptr_t>(SlotAddressSigned);

		if (SlotAddress < pImageBase || SlotAddress + sizeof(std::uintptr_t) > pImageBase + uImageSize)
			continue;

		const auto SlotOffset = SlotAddress - pImageBase;
		const auto ApiAddress = *reinterpret_cast<std::uintptr_t*>(pImage + SlotOffset);

		if (ApiAddress == 0)
			continue;

		bool is_suspected = false;

		auto api = VMPCore::sApiReader.getApiByVirtualAddress(ApiAddress, &is_suspected);

		if (api == 0)
			continue;


		if (api->module->modBaseAddr == pImageBase || api->module->modBaseAddr == reinterpret_cast<std::uintptr_t>(pImage))
			continue;

		const auto AlreadyExists = std::any_of(
			VMPCore::vecPatchInfo.begin(),
			VMPCore::vecPatchInfo.end(),
			[PatchAddress](const VMPCore::S_IatPatchInfo& Info)
			{
				return Info.m_pPatchAddress == PatchAddress;
			});

		if (AlreadyExists)
			continue;

		VMPCore::S_IatPatchInfo PatchInfo{};
		PatchInfo.m_iCallIatMode = VMPCore::CALL_IAT_COMMON;
		PatchInfo.m_iIatEncryptMode = VMPCore::IAT_ENCRYPT_UNKNOWN;
		PatchInfo.m_pPatchAddress = PatchAddress;
		PatchInfo.m_pBaseModule = api->module->modBaseAddr;
		PatchInfo.m_pApiAddress = ApiAddress;

		VMPCore::vecPatchInfo.emplace_back(std::move(PatchInfo));
		spdlog::info("Direct IAT call detected at 0x{0:x} targeting 0x{1:x} - {2}", PatchAddress, ApiAddress, api->name);
	}
}


bool VMPCore::DumpModule(const std::string& outputPath)
{
	auto* pBase = reinterpret_cast<std::uint8_t*>(pImageBuffer);
	auto* pDosHeader = reinterpret_cast<IMAGE_DOS_HEADER*>(pBase);

	if (pDosHeader->e_magic != IMAGE_DOS_SIGNATURE)
	{
		spdlog::error("Invalid DOS signature in buffer");
		return false;
	}

	auto* pNtHeaders = reinterpret_cast<IMAGE_NT_HEADERS*>(pBase + pDosHeader->e_lfanew);

	if (pNtHeaders->Signature != IMAGE_NT_SIGNATURE)
	{
		spdlog::error("Invalid NT signature in buffer");
		return false;
	}

	// ── Step 1: Convert existing sections to file layout ────────────────
	auto* pSectionHeader = IMAGE_FIRST_SECTION(pNtHeaders);
	DWORD sectionAlignment = pNtHeaders->OptionalHeader.SectionAlignment;
	DWORD fileAlignment = pNtHeaders->OptionalHeader.FileAlignment;

	DWORD dwOrigFileSize = 0;
	for (WORD i = 0; i < pNtHeaders->FileHeader.NumberOfSections; i++)
	{
		auto& sec = pSectionHeader[i];
		sec.PointerToRawData = sec.VirtualAddress;
		sec.SizeOfRawData = sec.Misc.VirtualSize;

		DWORD secEnd = sec.PointerToRawData + sec.SizeOfRawData;
		if (secEnd > dwOrigFileSize)
			dwOrigFileSize = secEnd;
	}
	if (dwOrigFileSize > k32ImageSize)
		dwOrigFileSize = static_cast<DWORD>(k32ImageSize);

	// ── Step 2: Build new section content (.vimp) ───────────────────────
	// Layout: [IAT entries] [align] [import descriptors] [dll names + INT arrays + hint/name entries]
	std::vector<std::uint8_t> vecSectionData;

	// IAT entries
	auto iatOffsetInSection = vecSectionData.size();
	vecSectionData.insert(vecSectionData.end(), vecIatBuffer.begin(), vecIatBuffer.end());

	// Align to 8
	while (vecSectionData.size() & 7)
		vecSectionData.push_back(0);

	// Compute new section RVA (aligned to SectionAlignment after last section)
	auto& lastSec = pSectionHeader[pNtHeaders->FileHeader.NumberOfSections - 1];
	DWORD lastSecEnd = lastSec.VirtualAddress + lastSec.Misc.VirtualSize;
	DWORD newSectionRva = (lastSecEnd + sectionAlignment - 1) & ~(sectionAlignment - 1);

	// Now we know the RVA, build import descriptors with correct addresses.
	auto descriptorOffset = vecSectionData.size();
	auto numModules = vecModuleList.size();
	auto descriptorArraySize = (numModules + 1) * sizeof(IMAGE_IMPORT_DESCRIPTOR);

	// Reserve space for descriptors (fill later)
	auto descriptorStart = vecSectionData.size();
	vecSectionData.resize(vecSectionData.size() + descriptorArraySize, 0);

	int iatIndex = 0;
	int descIndex = 0;

	// Temporary storage for descriptor data (we'll write after building everything)
	struct DescInfo {
		DWORD nameRva;
		DWORD oftRva;
		DWORD ftRva;
	};
	std::vector<DescInfo> descInfos;

	for (const auto& [moduleBase, apiSet] : mapImportEchmoduleApi)
	{
		DescInfo di{};

		// DLL name string
		ModuleInfo sTempModule{};
		GetModulePathByAddress(moduleBase, sTempModule);
		const WCHAR* wName = sTempModule.getFilename();
		char dllName[MAX_PATH];
		WideCharToMultiByte(CP_ACP, 0, wName, -1, dllName, MAX_PATH, nullptr, nullptr);
		auto dllNameLen = strlen(dllName) + 1;

		di.nameRva = newSectionRva + static_cast<DWORD>(vecSectionData.size());
		vecSectionData.insert(vecSectionData.end(), dllName, dllName + dllNameLen);
		if (vecSectionData.size() & 1) vecSectionData.push_back(0);

		// OriginalFirstThunk (INT) array
		di.oftRva = newSectionRva + static_cast<DWORD>(vecSectionData.size());
		auto intEntryCount = apiSet.size() + 1;
		auto intArraySize = intEntryCount * sizeof(IMAGE_THUNK_DATA64);
		auto intArrayStart = vecSectionData.size();
		vecSectionData.resize(vecSectionData.size() + intArraySize, 0);
		auto* pIntArray = reinterpret_cast<IMAGE_THUNK_DATA64*>(vecSectionData.data() + intArrayStart);

		// FirstThunk points to IAT entries at start of section
		di.ftRva = newSectionRva + static_cast<DWORD>(iatOffsetInSection) + iatIndex * sizeof(std::uintptr_t);

		// Hint/Name entries for each API
		int apiIdx = 0;
		for (auto pApiAddress : apiSet)
		{
			bool isSuspect = false;
			auto* apiInfo = sApiReader.getApiByVirtualAddress(static_cast<DWORD_PTR>(pApiAddress), &isSuspect);

			if (vecSectionData.size() & 1) vecSectionData.push_back(0);

			if (apiInfo && apiInfo->name[0] != '\0')
			{
				auto hintNameRva = newSectionRva + static_cast<DWORD>(vecSectionData.size());
				// WORD hint
				vecSectionData.push_back(apiInfo->hint & 0xFF);
				vecSectionData.push_back((apiInfo->hint >> 8) & 0xFF);
				// name string
				auto nameLen = strlen(apiInfo->name) + 1;
				vecSectionData.insert(vecSectionData.end(), apiInfo->name, apiInfo->name + nameLen);

				pIntArray[apiIdx].u1.AddressOfData = hintNameRva;
			}
			else
			{
				WORD ordinal = apiInfo ? apiInfo->ordinal : 0;
				pIntArray[apiIdx].u1.Ordinal = IMAGE_ORDINAL_FLAG64 | ordinal;
			}
			apiIdx++;
		}

		iatIndex += static_cast<int>(apiSet.size()) + 1;
		descInfos.push_back(di);
		descIndex++;
	}

	// Fill in the descriptor array
	auto* pDescriptors = reinterpret_cast<IMAGE_IMPORT_DESCRIPTOR*>(vecSectionData.data() + descriptorStart);
	for (size_t i = 0; i < descInfos.size(); i++)
	{
		pDescriptors[i].OriginalFirstThunk = descInfos[i].oftRva;
		pDescriptors[i].Name = descInfos[i].nameRva;
		pDescriptors[i].FirstThunk = descInfos[i].ftRva;
		pDescriptors[i].TimeDateStamp = 0;
		pDescriptors[i].ForwarderChain = 0;
	}

	// Align section size to FileAlignment
	DWORD newSectionRawSize = static_cast<DWORD>(vecSectionData.size());
	DWORD newSectionAlignedSize = (newSectionRawSize + fileAlignment - 1) & ~(fileAlignment - 1);
	vecSectionData.resize(newSectionAlignedSize, 0);

	// ── Step 3: Add new section header ──────────────────────────────────
	// Align PointerToRawData to FileAlignment (PE spec requirement)
	DWORD newSectionFileOffset = (dwOrigFileSize + fileAlignment - 1) & ~(fileAlignment - 1);

	auto* pNewSec = &pSectionHeader[pNtHeaders->FileHeader.NumberOfSections];
	memset(pNewSec, 0, sizeof(IMAGE_SECTION_HEADER));
	memcpy(pNewSec->Name, ".vimp\0\0\0", 8);
	pNewSec->Misc.VirtualSize = newSectionRawSize;
	pNewSec->VirtualAddress = newSectionRva;
	pNewSec->SizeOfRawData = newSectionAlignedSize;
	pNewSec->PointerToRawData = newSectionFileOffset;
	pNewSec->Characteristics = IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE;

	pNtHeaders->FileHeader.NumberOfSections += 1;

	// Update SizeOfImage
	DWORD newImageSize = newSectionRva + ((newSectionRawSize + sectionAlignment - 1) & ~(sectionAlignment - 1));
	pNtHeaders->OptionalHeader.SizeOfImage = newImageSize;

	// ── Step 4: Update PE data directories ──────────────────────────────
	auto& importDir = pNtHeaders->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT];
	importDir.VirtualAddress = newSectionRva + static_cast<DWORD>(descriptorOffset);
	importDir.Size = static_cast<DWORD>(numModules * sizeof(IMAGE_IMPORT_DESCRIPTOR));

	auto& iatDir = pNtHeaders->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IAT];
	iatDir.VirtualAddress = newSectionRva + static_cast<DWORD>(iatOffsetInSection);
	iatDir.Size = static_cast<DWORD>(k32IatSize);

	// ── Step 5: Update pIatAddress for patches ──────────────────────────
	// Recompute all patch IAT addresses: old pIatAddress was a placeholder,
	// now replace with actual RVA-based address.
	auto newIatBase = pImageLoadAddress + newSectionRva + iatOffsetInSection;
	auto oldIatBase = pIatAddress;
	for (auto& sIatPatchInfo : vecPatchInfo)
	{
		if (sIatPatchInfo.m_pIatAddress >= oldIatBase &&
			sIatPatchInfo.m_pIatAddress < oldIatBase + k32IatSize)
		{
			sIatPatchInfo.m_pIatAddress = newIatBase + (sIatPatchInfo.m_pIatAddress - oldIatBase);
		}
	}
	pIatAddress = newIatBase;

	// Re-apply patches with corrected IAT addresses
	ApplyPatches();

	spdlog::info("New section .vimp at RVA {:X}, size {:X}", newSectionRva, newSectionAlignedSize);
	spdlog::info("Import table: {} modules, IAT RVA: {:X}, Import RVA: {:X}",
		numModules, newSectionRva + static_cast<DWORD>(iatOffsetInSection),
		newSectionRva + static_cast<DWORD>(descriptorOffset));

	// ── Step 6: Write file ──────────────────────────────────────────────
	HANDLE hFile = CreateFileA(outputPath.c_str(), GENERIC_WRITE, 0, nullptr, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, nullptr);
	if (hFile == INVALID_HANDLE_VALUE)
	{
		spdlog::error("Cannot create output file: {0}, error: {1}", outputPath, GetLastError());
		return false;
	}

	DWORD dwWritten = 0;
	// Write original module data
	WriteFile(hFile, pBase, dwOrigFileSize, &dwWritten, nullptr);

	// Pad to aligned file offset for new section
	if (newSectionFileOffset > dwOrigFileSize)
	{
		std::vector<std::uint8_t> padding(newSectionFileOffset - dwOrigFileSize, 0);
		DWORD dwPadWritten = 0;
		WriteFile(hFile, padding.data(), static_cast<DWORD>(padding.size()), &dwPadWritten, nullptr);
		dwWritten += dwPadWritten;
	}

	// Append new section
	DWORD dwWritten2 = 0;
	WriteFile(hFile, vecSectionData.data(), static_cast<DWORD>(vecSectionData.size()), &dwWritten2, nullptr);

	CloseHandle(hFile);

	spdlog::info("Module dumped to {0} ({1} bytes)", outputPath, dwWritten + dwWritten2);
	return true;
}

int main(int argc, char** argv)
{
	argparse::ArgumentParser cProgram("VMP-Imports-Deobfuscator");

	cProgram.add_argument("-p", "--pid")
		.help("Target process name")
		.required()
		.scan<'d', int>();

	cProgram.add_argument("-m", "--module")
		.help("Target module name")
		.default_value<std::string>("");

	cProgram.add_argument("-i", "--iat")
		.help("section that is used to storage new IAT, it maybe destroy vmp code")
		.default_value<std::string>(".rdata");

	cProgram.add_argument("-o", "--output")
		.help("Output path for the dumped PE file")
		.default_value<std::string>("dumped.dll");

	try
	{
		cProgram.parse_args(argc, argv);
	}
	catch (const std::runtime_error& err)
	{
		std::cerr << err.what() << std::endl;
		std::cerr << cProgram;
		std::exit(1);
	}

	// @note: @colby57: Retrieve values of parsed command line arguments.
	auto iProcessId = cProgram.get<int>("--pid");
	auto sNewIat = cProgram.get<std::string>("--iat");
	auto sModuleName = cProgram.get<std::string>("--module");
	auto sOutputPath = cProgram.get<std::string>("--output");

	Process sProcess{};

	// @note: @colby57: Attempt to attach to the target process.
	if (NT_SUCCESS(sProcess.Attach(iProcessId)))
	{
		// @note: @colby57: Access the target process memory and modules.
		auto& sMemory = sProcess.memory();
		auto& sModules = sProcess.modules();

		auto& sCore = sProcess.core();

		// @note: @colby57: Check if process is 32-bit
		if (sCore.isWow64())
		{
			spdlog::error("32-bit applications are not yet supported!\n");
			sProcess.Detach();
			return 0;
		}

		// @note: @colby57: Get information about the target module.
		auto sTargetModule = sModuleName == "" ? sModules.GetMainModule() : sModules.GetModule(std::wstring(sModuleName.begin(), sModuleName.end()));

		if (!sTargetModule)
		{
			spdlog::error("Failed to find module {} in process", sModuleName.c_str());
			return 0;
		}

		// @note: @colby57: Allocate a buffer to store the PE image of the target module.
		const auto pBuffer = malloc(sTargetModule->size);

		if (!pBuffer)
		{
			spdlog::error("Allocate PE Image buffer failed");
			return 0;
		}

		// @note: @colby57: Initialize global variables with module information.
		VMPCore::pImageLoadAddress = sTargetModule->baseAddress;
		VMPCore::k32ImageSize = sTargetModule->size;
		VMPCore::pImageBuffer = reinterpret_cast<std::uintptr_t>(pBuffer);

		// Read the target module page-by-page, forcing PAGE_EXECUTE_READWRITE
		// on each region first to handle VMP self-remapped pages.
		memset(pBuffer, 0, sTargetModule->size);
		bool bReadSuccess = true;
		{
			const auto moduleBase = sTargetModule->baseAddress;
			const auto moduleEnd = moduleBase + sTargetModule->size;
			auto currentAddr = moduleBase;

			while (currentAddr < moduleEnd)
			{
				MEMORY_BASIC_INFORMATION64 mbi{};
				if (!NT_SUCCESS(sMemory.Query(currentAddr, &mbi)))
				{
					spdlog::warn("VirtualQuery failed at {:X}, skipping page", currentAddr);
					currentAddr += 0x1000;
					continue;
				}

				const auto regionBase = static_cast<uintptr_t>(mbi.BaseAddress);
				const auto regionEnd = regionBase + mbi.RegionSize;
				const auto readStart = max(currentAddr, regionBase);
				const auto readEnd = min(moduleEnd, regionEnd);
				const auto readSize = readEnd - readStart;
				const auto bufferOffset = readStart - moduleBase;

				if (mbi.State != MEM_COMMIT)
				{
					spdlog::debug("Skipping non-committed region at {:X} (state {:X})", readStart, mbi.State);
					currentAddr = regionEnd;
					continue;
				}

				DWORD dwOldProtect = 0;
				bool bProtectChanged = false;

				if (mbi.Protect & (PAGE_NOACCESS | PAGE_GUARD) || mbi.Protect == 0)
				{
					if (NT_SUCCESS(sMemory.Protect(readStart, readSize, PAGE_EXECUTE_READWRITE, &dwOldProtect)))
					{
						bProtectChanged = true;
						spdlog::debug("Changed protection at {:X} from {:X} to RWX", readStart, mbi.Protect);
					}
					else
					{
						spdlog::warn("Failed to change protection at {:X}, skipping", readStart);
						currentAddr = regionEnd;
						continue;
					}
				}

				auto readStatus = sMemory.Read(readStart, readSize, static_cast<uint8_t*>(pBuffer) + bufferOffset);
				if (!NT_SUCCESS(readStatus))
				{
					spdlog::warn("Read failed at {:X} size {:X} status {:X}", readStart, readSize, readStatus);
				}

				if (bProtectChanged)
				{
					sMemory.Protect(readStart, readSize, dwOldProtect);
				}

				currentAddr = regionEnd;
			}

			spdlog::info("Page-by-page read completed for module at {:X}", moduleBase);
		}
		if (bReadSuccess)
		{
			// @note: @colby57: Parse the PE image to extract information about its sections.
			PEImage sPeImage;
			sPeImage.Parse(pBuffer);



			for (auto sSection : sPeImage.sections())
				VMPCore::vecProcessSections.emplace_back(sSection);

			const auto sExcludeSections = GetVmpSections(sMemory);

			// Use a placeholder IAT address (will be replaced in DumpModule with the actual new section RVA).
			VMPCore::pIatAddress = VMPCore::pImageLoadAddress;
			VMPCore::bUseIatSection = true;

			// @note: @colby57: Iterate through sections, searching for specific patterns and filtering addresses.
			for (auto sSection : sPeImage.sections())
			{

				spdlog::info("scanning section {}", (char*)sSection.Name);
				if ((sSection.Characteristics & IMAGE_SCN_MEM_EXECUTE) &&
					std::find(sExcludeSections.begin(), sExcludeSections.end(), (char*)sSection.Name) == sExcludeSections.end())
				{

					spdlog::info("scanning section enter {}", (char*)sSection.Name);
					// @note: @colby57: Search for a specific pattern in the target section.
					{
						PatternSearch sPattern({ 0xE8,'?','?','?','?' });
						std::vector<ptr_t> vecResults{};

						if (sPattern.SearchRemote(
							sProcess,
							'?',
							sTargetModule->baseAddress + sSection.VirtualAddress,
							sSection.Misc.VirtualSize,
							vecResults,
							SIZE_MAX) != 0)
						{
							// @note: @colby57: Filter addresses based on certain criteria.
							FilterAddresses(
								sTargetModule->baseAddress,
								sTargetModule->size,
								pBuffer,
								VMPCore::vecPatternAddressList,
								vecResults,
								sSection.VirtualAddress,
								sSection.Misc.VirtualSize);
						}
					}



				}
			}

			sProcess.Detach();

			// @note: @colby57: Initialize the Unicorn emulator with the PE image buffer.
			const auto Status = Emulator::Init(pBuffer);

			if (!Status)
			{
				spdlog::error("Cannot initialize emulator.\n");
				free(pBuffer);
				return 0;
			}

			// @note: @colby57: Open a handle to the target process and retrieve module information.
			if (!ProcessAccessHelp::openProcessHandle(iProcessId))
			{
				spdlog::error("Open Process Failed\n");
				free(pBuffer);
				return 0;
			}

			// @note: @colby57: Retrieve module information from the current and target processes.
			if (!ProcessAccessHelp::getProcessModules(GetCurrentProcess(), ProcessAccessHelp::ownModuleList) ||
				!ProcessAccessHelp::getProcessModules(ProcessAccessHelp::hProcess, ProcessAccessHelp::moduleList))
			{
				spdlog::error("Cannot get process modules\n");
				ProcessAccessHelp::closeProcessHandle();
				free(pBuffer);
			}

			// @note: @colby57: Read APIs from module list and store in the ApiReader instance.
			VMPCore::sApiReader.readApisFromModuleList();

			// @note: @colby57: Emulate patterns for each specified pattern address.
			for (auto Address : VMPCore::vecPatternAddressList)
			{
				VMPCore::pCurrentPatternAddress = Address;
				Emulator::Start(VMPCore::pCurrentPatternAddress);
			}



			// @note: @baier233: Locate the unencrypted IAT calls, add them to the new IAT table, and subsequently redirect the addresses of the IAT calls to the new IAT table.
			sProcess.Attach(iProcessId);

			for (auto sSection : sPeImage.sections())
			{
				if ((sSection.Characteristics & IMAGE_SCN_MEM_EXECUTE) &&
					std::find(sExcludeSections.begin(), sExcludeSections.end(), (char*)sSection.Name) == sExcludeSections.end())
				{

					{

						PatternSearch sPattern({ 0XFF,0X15,'?','?','?','?' });
						std::vector<ptr_t> vecDirectCallResults{};

						if (sPattern.SearchRemote(
							sProcess,
							'?',
							sTargetModule->baseAddress + sSection.VirtualAddress,
							sSection.Misc.VirtualSize,
							vecDirectCallResults,
							SIZE_MAX) != 0)
						{

							CollectDirectIatCalls(sTargetModule->baseAddress,
								sTargetModule->size,
								pBuffer,
								vecDirectCallResults);
						}
					}


					{
						PatternSearch sPattern48({ 0X48, 0X8B, '?', '?', '?', '?', '?' });
						std::vector<ptr_t> vecMovResults{};

						if (sPattern48.SearchRemote(
							sProcess,
							'?',
							sTargetModule->baseAddress + sSection.VirtualAddress,
							sSection.Misc.VirtualSize,
							vecMovResults,
							SIZE_MAX) != 0)
						{
							CollectMovIatReferences(
								sTargetModule->baseAddress,
								sTargetModule->size,
								pBuffer,
								vecMovResults);
						}

						PatternSearch sPattern4C({ 0X4C, 0X8B, '?', '?', '?', '?', '?' });
						std::vector<ptr_t> vecMovResults4C{};

						if (sPattern4C.SearchRemote(
							sProcess,
							'?',
							sTargetModule->baseAddress + sSection.VirtualAddress,
							sSection.Misc.VirtualSize,
							vecMovResults4C,
							SIZE_MAX) != 0)
						{
							CollectMovIatReferences(
								sTargetModule->baseAddress,
								sTargetModule->size,
								pBuffer,
								vecMovResults4C);
						}
					}


				}
			}

			sProcess.Detach();



			// @note: @colby57: Retrieve information about IAT modules, import module API lists, and fix IAT in memory.
			VMPCore::ParseModules();
			VMPCore::ParseApiList();

			if (!VMPCore::PatchCalls())
			{
				spdlog::critical("bruh!");

				ProcessAccessHelp::closeProcessHandle();
				free(pBuffer);

				return 0;
			}

			if (!VMPCore::DumpModule(sOutputPath))
			{
				spdlog::error("Failed to dump module!");
				ProcessAccessHelp::closeProcessHandle();
				free(pBuffer);
				return 0;
			}

			ProcessAccessHelp::closeProcessHandle();
			free(pBuffer);
		}
		else
		{
			spdlog::error("Failed to read PE Image!");

			ProcessAccessHelp::closeProcessHandle();
			free(pBuffer);

			return 0;
		}
	}
	else
	{
		spdlog::error("Attach Failed\n");
		return 0;
	}

	spdlog::info("All imports fixed! Enjoy!");
	return 0;
}